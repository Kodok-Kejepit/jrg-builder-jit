//! Bytecode → Cranelift IR (`dokumentasi/jit/j2-rencana.md`, `j4-rencana.md`). Tiap posisi stack abstrak
//! = satu variabel `i64`. Jaga yang gagal dan titik keluar mencatat keadaan bingkai lewat `deopt::catat`
//! lalu keluar; status 0 berhasil, 1 deopt, 2 panggilan belum dimulai.

use cranelift_codegen::ir::{condcodes::{FloatCC, IntCC}, types, AbiParam, Block, FuncRef, InstBuilder, MemFlagsData, Signature, StackSlot, StackSlotData, StackSlotKind, Type, Value};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{FuncId, Module};

use super::layak::{Cara, Jenis, Rencana};
use crate::vm::opcode::OpCode;
use crate::vm::value::VmFunction;

pub const BERHASIL: i64 = 0;
/// Bingkai native sudah dicatat (yang paling dalam lebih dulu); VM melanjutkannya.
pub const DEOPT: i64 = 1;
/// Callee keluar sebelum mulai (terlalu dalam): pemanggilnya deopt DI instruksi `Call`, VM yang memanggil.
pub const ULANG: i64 = 2;
/// Berhasil, hasilnya pecahan (bitnya di `keluar`).
pub const BERHASIL_PECAHAN: i64 = 4;
/// Berhasil, hasilnya `bool` (cuma kode yang dimasuki dari VM, `KEMBALI_SKALAR`).
pub const BERHASIL_BOOL: i64 = 3;
/// Instruksi yang dijalankan VM dari dalam kode native gagal; galatnya di `lambat::ambil_galat`.
pub const GAGAL: i64 = 5;
/// Berhasil, hasilnya nilai milik VM di posisi `keluar` bingkai (cuma `KEMBALI_SKALAR`).
pub const BERHASIL_NILAI: i64 = 6;
/// `ReturnNil` (cuma `KEMBALI_SKALAR`).
pub const BERHASIL_UNIT: i64 = 7;
/// Kedalaman panggilan native paling banyak; `panggil::coba` menurunkannya mendekati batas bingkai VM.
pub const KEDALAMAN_MAKS: i64 = 4096;

/// `fn(args: *const i64, kedalaman: i32, keluar: *mut i64) -> i32`, satu bentuk untuk semua.
pub fn tanda_tangan(m: &impl Module, cc: CallConv) -> Signature {
    let ptr = m.target_config().pointer_type();
    let mut sig = Signature::new(cc);
    sig.params.push(AbiParam::new(ptr));
    sig.params.push(AbiParam::new(types::I32));
    sig.params.push(AbiParam::new(ptr));
    sig.returns.push(AbiParam::new(types::I32));
    sig
}

/// `deopt::catat(fid, ip, nilai, n)`.
pub fn tanda_tangan_catat(m: &impl Module, cc: CallConv) -> Signature {
    let ptr = m.target_config().pointer_type();
    let mut sig = Signature::new(cc);
    for t in [types::I32, types::I32, ptr, types::I32] { sig.params.push(AbiParam::new(t)); }
    sig
}

/// `deopt::undi() -> i32`.
pub fn tanda_tangan_undi(cc: CallConv) -> Signature {
    let mut sig = Signature::new(cc);
    sig.returns.push(AbiParam::new(types::I32));
    sig
}

/// `lambat::baca(rel, i, keluar) -> i32`.
pub fn tanda_tangan_baca(m: &impl Module, cc: CallConv) -> Signature {
    let mut sig = Signature::new(cc);
    for t in [types::I64, types::I64, m.target_config().pointer_type()] { sig.params.push(AbiParam::new(t)); }
    sig.returns.push(AbiParam::new(types::I32));
    sig
}

/// `lambat::tulis(rel, i, nilai, jenis) -> i32`.
pub fn tanda_tangan_tulis(cc: CallConv) -> Signature {
    let mut sig = Signature::new(cc);
    for t in [types::I64, types::I64, types::I64, types::I32] { sig.params.push(AbiParam::new(t)); }
    sig.returns.push(AbiParam::new(types::I32));
    sig
}

/// Tanda tangan fungsi `lambat` lainnya (`i64` dan penunjuk sama lebar di sasaran JIT).
pub fn tanda_tangan_umum(cc: CallConv, param: &[Type], hasil: Option<Type>) -> Signature {
    let mut sig = Signature::new(cc);
    for t in param { sig.params.push(AbiParam::new(*t)); }
    if let Some(h) = hasil { sig.returns.push(AbiParam::new(h)); }
    sig
}

/// Fungsi `lambat` di luar `baca`/`tulis`.
pub struct ImporLambat {
    pub langkah: FuncId, pub muat: FuncId, pub buang: FuncId, pub benar: FuncId, pub buka: FuncId,
    pub taruh: FuncId, pub ambil: FuncId, pub simpan: FuncId, pub pola: FuncId, pub payload: FuncId,
    pub pola_lokal: FuncId, pub payload_lokal: FuncId, pub buka_lokal: FuncId,
    pub iter_ada: FuncId, pub maju: FuncId, pub langkah_cabang: FuncId, pub sebar: FuncId,
    pub pindah: FuncId, pub muat_global: FuncId, pub simpan_global: FuncId, pub indeks: FuncId, pub field: FuncId,
    pub masuk: FuncId, pub keluar: FuncId, pub salin: FuncId, pub tukar: FuncId, pub cek_metode: FuncId,
    pub bawaan: FuncId, pub biner: FuncId, pub muat_upval: FuncId, pub simpan_upval: FuncId,
}

/// Fungsi impor dan identitas bingkai untuk blok deopt.
pub struct Impor<'a> {
    pub catat: FuncId, pub undi: Option<FuncId>, pub baca: FuncId, pub tulis: FuncId, pub fid: u32,
    pub lambat: &'a ImporLambat,
}

/// Kembali dengan status `st` tanpa mencatat apa pun.
fn kembali_status(b: &mut FunctionBuilder, st: i64) {
    let v = b.ins().iconst(types::I32, st);
    b.ins().return_(&[v]);
}

/// `bendera`: `BUKA_SUDAH` selama sisa instruksi `Cara::Buka` sesudah bukaannya berhasil.
struct Keluar { catat: FuncRef, fid: i64, ptr: Type, slot: StackSlot, bendera: std::cell::Cell<i64> }

/// Bit `ip` deopt: posisi yang dibuka instruksi itu sudah berisi angka native (`deopt::pulihkan`).
pub const BUKA_SUDAH: i64 = 1 << 30;
/// Bit `ip` deopt: jaga spekulasi yang gagal (`PintuJit::tandai_spek_gagal`).
pub const GAGAL_SPEK: i64 = 1 << 29;
/// Bit `ip` deopt: puncak stack masih milik VM (hasil instruksi sebelumnya yang spekulasinya gagal).
pub const PUNCAK_VM: i64 = 1 << 28;

/// Blok saat ini menjadi keluar deopt: nilai stack `jenis` dicatat untuk dilanjutkan VM di `ip`.
fn keluar_deopt(b: &mut FunctionBuilder, k: &Keluar, var: &[Variable], ip: usize, jenis: &[Jenis]) {
    let slot = k.slot;
    for (i, j) in jenis.iter().enumerate() {
        // Fungsi, `nil` dan nilai milik VM tidak punya isi native; `deopt::pulihkan` membangunnya.
        if !matches!(j, Jenis::Bulat | Jenis::Bool | Jenis::Pecahan) { continue; }
        let v = b.use_var(var[i]);
        b.ins().stack_store(k.ptr, v, slot, (i * 8) as i32);
    }
    let pn = b.ins().stack_addr(k.ptr, slot, 0);
    let fid = b.ins().iconst(types::I32, k.fid);
    let ipv = b.ins().iconst(types::I32, ip as i64 | k.bendera.get());
    let n = b.ins().iconst(types::I32, jenis.len() as i64);
    b.ins().call(k.catat, &[fid, ipv, pn, n]);
    let st = b.ins().iconst(types::I32, DEOPT);
    b.ins().return_(&[st]);
}

/// `cond` benar = deopt di `ip` dengan stack `jenis`; sesudahnya builder ada di blok lanjutan.
fn jaga(b: &mut FunctionBuilder, k: &Keluar, var: &[Variable], cond: Value, ip: usize, jenis: &[Jenis]) {
    let d = b.create_block();
    b.set_cold_block(d);
    let terus = b.create_block();
    b.ins().brif(cond, d, &[], terus, &[]);
    b.switch_to_block(d);
    keluar_deopt(b, k, var, ip, jenis);
    b.switch_to_block(terus);
}

/// `jaga` atas spekulasi: kegagalannya dicatat supaya kompilasi berikutnya tidak berspekulasi lagi.
fn jaga_spek(b: &mut FunctionBuilder, k: &Keluar, var: &[Variable], cond: Value, ip: usize, jenis: &[Jenis]) {
    let lama = k.bendera.get();
    k.bendera.set(lama | GAGAL_SPEK);
    jaga(b, k, var, cond, ip, jenis);
    k.bendera.set(lama);
}

/// Hasil spekulatif (`Rencana::spek`) di posisi `pos` dibuka jadi `j`; gagal = deopt di `lanjut` dengan
/// puncak milik VM, dan spekulasinya tidak diulang.
#[allow(clippy::too_many_arguments)]
fn buka_hasil(
    b: &mut FunctionBuilder, k: &Keluar, var: &[Variable], r: &Rencana, buka: FuncRef, wadah: StackSlot,
    lanjut: usize, pos: usize, j: Jenis,
) {
    let pk = b.ins().stack_addr(k.ptr, wadah, 0);
    let pv = b.ins().iconst(types::I64, pos as i64);
    let jv = b.ins().iconst(types::I32, if j == Jenis::Pecahan { 5 } else { 1 });
    let c = b.ins().call(buka, &[pv, jv, pk]);
    let st = b.inst_results(c)[0];
    let lama = k.bendera.replace(PUNCAK_VM | GAGAL_SPEK);
    jaga(b, k, var, st, lanjut, r.keadaan[lanjut].as_ref().expect("penerus hasil terjangkau"));
    k.bendera.set(lama);
    let v = b.ins().stack_load(k.ptr, types::I64, wadah, 0);
    b.def_var(var[pos], v);
}

/// Nilai angka jadi `f64`: pecahan dibaca bitnya, bulat dikonversi seperti `i128 as f64` acuan.
fn ke_f64(b: &mut FunctionBuilder, v: Value, j: Jenis) -> Value {
    if j == Jenis::Pecahan { b.ins().bitcast(types::F64, MemFlagsData::new(), v) }
    else { b.ins().fcvt_from_sint(types::F64, v) }
}

fn dari_f64(b: &mut FunctionBuilder, f: Value) -> Value {
    b.ins().bitcast(types::I64, MemFlagsData::new(), f)
}

/// Posisi `rentang` milik kode native ke slot rekaman (`lambat::langkah` menyalinnya ke stack VM);
/// fungsi yang dimuat kode native (`LoadGlobal`) ditaruh langsung sebagai nilai VM-nya.
#[allow(clippy::too_many_arguments)]
fn tumpahkan(
    b: &mut FunctionBuilder, var: &[Variable], s: &[Jenis], rentang: std::ops::Range<usize>,
    slot: StackSlot, ptr: Type, taruh: FuncRef, callee: &[crate::vm::value::VmValue],
) {
    for i in rentang {
        if let Jenis::Fungsi(c) = s[i] {
            let ke = b.ins().iconst(types::I64, i as i64);
            let kv = b.ins().iconst(types::I64, &callee[c] as *const _ as i64);
            b.ins().call(taruh, &[ke, kv]);
            continue;
        }
        if !matches!(s[i], Jenis::Bulat | Jenis::Bool | Jenis::Pecahan) { continue; }
        let v = b.use_var(var[i]);
        b.ins().stack_store(ptr, v, slot, (i * 8) as i32);
    }
}

pub fn turunkan(
    m: &mut impl Module,
    fungsi: &mut cranelift_codegen::ir::Function,
    fctx: &mut FunctionBuilderContext,
    f: &VmFunction,
    r: &Rencana,
    id_callee: &[Option<FuncId>],
    id_langsung: &[FuncId],
    impor: &Impor,
) {
    let ptr = m.target_config().pointer_type();
    let mut b = FunctionBuilder::new(fungsi, fctx);
    let var: Vec<Variable> = (0..r.maks.max(1)).map(|_| b.declare_var(types::I64)).collect();
    // Penyangga argumen dan hasil milik pemanggil: selaras, tidak pernah menjebak.
    let fl = MemFlagsData::trusted();
    let kode = &f.chunk.code;
    let blok: Vec<Option<Block>> = (0..kode.len())
        .map(|i| (r.pemimpin[i] && r.keadaan[i].is_some()).then(|| b.create_block())).collect();

    let masuk = b.create_block();
    b.append_block_params_for_function_params(masuk);
    b.switch_to_block(masuk);
    let (args, kedalaman, keluar) = {
        let p = b.block_params(masuk);
        (p[0], p[1], p[2])
    };
    // Satu slot rekaman untuk semua titik deopt fungsi ini (cuma satu yang pernah dipakai per panggilan).
    let slot = b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, (r.maks.max(1) * 8) as u32, 3));
    let k = Keluar { catat: m.declare_func_in_func(impor.catat, b.func), fid: impor.fid as i64, ptr, slot, bendera: Default::default() };
    let undi = impor.undi.map(|u| m.declare_func_in_func(u, b.func));
    let (baca, tulis) = (m.declare_func_in_func(impor.baca, b.func), m.declare_func_in_func(impor.tulis, b.func));
    let wadah = b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 3));
    let il = impor.lambat;
    let [f_langkah, f_muat, f_buang, f_benar, f_buka, f_taruh, f_ambil, f_simpan, f_pola, f_payload] =
        [il.langkah, il.muat, il.buang, il.benar, il.buka, il.taruh, il.ambil, il.simpan, il.pola, il.payload]
        .map(|id| m.declare_func_in_func(id, b.func));
    let [f_pola_lokal, f_payload_lokal, f_buka_lokal, f_iter_ada, f_maju, f_cabang, f_sebar] =
        [il.pola_lokal, il.payload_lokal, il.buka_lokal, il.iter_ada, il.maju, il.langkah_cabang, il.sebar]
        .map(|id| m.declare_func_in_func(id, b.func));
    let [f_pindah, f_muat_global, f_simpan_global, f_indeks, f_field, f_masuk, f_keluar, f_salin, f_tukar, f_cek_metode, f_bawaan, f_biner] =
        [il.pindah, il.muat_global, il.simpan_global, il.indeks, il.field, il.masuk, il.keluar, il.salin, il.tukar, il.cek_metode, il.bawaan, il.biner]
        .map(|id| m.declare_func_in_func(id, b.func));
    let [f_muat_upval, f_simpan_upval] = [il.muat_upval, il.simpan_upval]
        .map(|id| m.declare_func_in_func(id, b.func));
    let dalam = b.create_block();
    b.set_cold_block(dalam);
    // Kedalaman native dijaga di pintu masuk; parameter dimuat dari penyangga argumen.
    let terlalu = b.ins().icmp_imm_s(IntCC::SignedGreaterThan, kedalaman, KEDALAMAN_MAKS);
    let mulai = b.create_block();
    b.ins().brif(terlalu, dalam, &[], mulai, &[]);
    b.switch_to_block(mulai);
    // Isi bingkai di titik masuk; posisi tanpa isi native diberi nol supaya tiap variabel terdefinisi.
    let nol = b.ins().iconst(types::I64, 0);
    for v in &var { b.def_var(*v, nol); }
    for (i, j) in r.jenis_masuk.iter().enumerate() {
        if !matches!(j, Jenis::Bulat | Jenis::Bool | Jenis::Pecahan) { continue; }
        let v = b.ins().load(types::I64, fl, args, (i * 8) as i32);
        b.def_var(var[i], v);
    }
    let kedalaman1 = b.ins().iadd_imm_s(kedalaman, 1);
    b.ins().jump(blok[r.masuk].expect("titik masuk selalu pemimpin"), &[]);

    let mut terbuka = false;
    // `LoadLocal` milik VM yang digabung dengan instruksi sesudahnya: yang sudah dikerjakan / bukaan
    // instruksi sesudahnya sudah dikerjakan.
    let (mut lewati, mut dibuka) = (false, false);
    for ip in 0..kode.len() {
        let Some(s) = &r.keadaan[ip] else { terbuka = false; continue };
        if let Some(bl) = blok[ip] {
            if terbuka { b.ins().jump(bl, &[]); }
            b.switch_to_block(bl);
            terbuka = true;
        }
        if std::mem::take(&mut lewati) { continue; }
        k.bendera.set(0);
        // Sesudah bukaan gabungan, posisinya belum ada di stack VM: deopt acak cuma di instruksi pertamanya.
        if let (Some(u), false) = (undi, dibuka) {
            let c = b.ins().call(u, &[]);
            let c = b.inst_results(c)[0];
            jaga(&mut b, &k, &var, c, ip, s);
        }
        let t = s.len();
        if r.keluar[ip] {
            keluar_deopt(&mut b, &k, &var, ip, s);
            terbuka = false;
            continue;
        }
        let ins = kode[ip];
        let a = ins.arg as usize;
        let atas = |b: &mut FunctionBuilder, k: usize| b.use_var(var[t - k]);
        let i64c = |b: &mut FunctionBuilder, v: i64| b.ins().iconst(types::I64, v);
        let mut buka_s;
        let s: &Vec<Jenis> = match &r.cara[ip] {
            Cara::Asli => s,
            Cara::Buka(daftar) => {
                // Nilai milik VM yang dipakai sebagai angka: jaga jenisnya, lalu instruksinya asli.
                buka_s = s.clone();
                for &(p, j) in daftar {
                    buka_s[p] = j;
                    if dibuka { continue; }
                    let pk = b.ins().stack_addr(ptr, wadah, 0);
                    let (pv, jv) = (i64c(&mut b, p as i64), b.ins().iconst(types::I32, if j == Jenis::Pecahan { 5 } else { 1 }));
                    let c = b.ins().call(f_buka, &[pv, jv, pk]);
                    let st = b.inst_results(c)[0];
                    jaga_spek(&mut b, &k, &var, st, ip, s);
                    let v = b.ins().stack_load(ptr, types::I64, wadah, 0);
                    b.def_var(var[p], v);
                }
                dibuka = false;
                k.bendera.set(BUKA_SUDAH);
                &buka_s
            }
            Cara::Langkah { ambil, taruh, tumpah } => {
                // Operand milik kode native ke slot rekaman, lalu VM menjalankan instruksinya.
                tumpahkan(&mut b, &var, s, t - tumpah..t, slot, ptr, f_taruh, &r.callee_nilai);
                let args = [
                    i64c(&mut b, ip as i64), i64c(&mut b, s.as_ptr() as i64), i64c(&mut b, t as i64),
                    i64c(&mut b, *tumpah as i64), i64c(&mut b, (t - ambil + taruh) as i64),
                    b.ins().stack_addr(ptr, slot, 0),
                ];
                let c = b.ins().call(f_langkah, &args);
                let st = b.inst_results(c)[0];
                let (gagal, terus) = (b.create_block(), b.create_block());
                b.set_cold_block(gagal);
                b.ins().brif(st, gagal, &[], terus, &[]);
                b.switch_to_block(gagal);
                kembali_status(&mut b, GAGAL);
                b.switch_to_block(terus);
                continue;
            }
            Cara::Muat => {
                // Dipakai langsung oleh instruksi sesudahnya (bukan sasaran lompat): lokalnya dibaca di
                // tempat; gagal = deopt di sini, sebelum keduanya.
                let gabung = !r.pemimpin.get(ip + 1).copied().unwrap_or(true)
                    && r.keadaan.get(ip + 1).is_some_and(|k| k.is_some()) && !r.keluar[ip + 1];
                let d = i64c(&mut b, a as i64);
                match r.cara.get(ip + 1) {
                    Some(Cara::Pola) if gabung => {
                        let desc = i64c(&mut b, &f.chunk.constants[kode[ip + 1].arg as usize] as *const _ as i64);
                        let c = b.ins().call(f_pola_lokal, &[d, desc]);
                        let c = b.inst_results(c)[0];
                        let salah = b.ins().icmp_imm_u(IntCC::Equal, c, 2);
                        jaga(&mut b, &k, &var, salah, ip, s);
                        let v = b.ins().uextend(types::I64, c);
                        b.def_var(var[t], v);
                        lewati = true;
                        continue;
                    }
                    Some(Cara::Payload) if gabung => {
                        let ke = i64c(&mut b, t as i64);
                        let c = b.ins().call(f_payload_lokal, &[d, ke]);
                        let c = b.inst_results(c)[0];
                        jaga(&mut b, &k, &var, c, ip, s);
                        if let Some(j) = r.spek[ip + 1] { buka_hasil(&mut b, &k, &var, r, f_buka, wadah, ip + 2, t, j); }
                        lewati = true;
                        continue;
                    }
                    // Semua bukaan instruksi sesudahnya dikerjakan di sini, jadi deopt-nya tetap di `ip`.
                    Some(Cara::Buka(daftar)) if gabung && daftar.iter().any(|(p, _)| *p == t) => {
                        for &(p, j) in daftar {
                            let pk = b.ins().stack_addr(ptr, wadah, 0);
                            let jv = b.ins().iconst(types::I32, if j == Jenis::Pecahan { 5 } else { 1 });
                            let c = if p == t { b.ins().call(f_buka_lokal, &[d, jv, pk]) } else {
                                let pv = i64c(&mut b, p as i64);
                                b.ins().call(f_buka, &[pv, jv, pk])
                            };
                            let c = b.inst_results(c)[0];
                            jaga_spek(&mut b, &k, &var, c, ip, s);
                            let v = b.ins().stack_load(ptr, types::I64, wadah, 0);
                            b.def_var(var[p], v);
                        }
                        dibuka = true;
                        continue;
                    }
                    _ => {}
                }
                let ke = i64c(&mut b, t as i64);
                b.ins().call(f_muat, &[d, ke]);
                continue;
            }
            Cara::Konstanta => {
                let k = if ins.op == OpCode::Const { &f.chunk.constants[a] as *const _ as i64 } else { 0 };
                let (ke, kv) = (i64c(&mut b, t as i64), i64c(&mut b, k));
                b.ins().call(f_taruh, &[ke, kv]);
                continue;
            }
            Cara::Ambil => {
                let (d, ke) = (i64c(&mut b, a as i64), i64c(&mut b, t as i64));
                b.ins().call(f_ambil, &[d, ke]);
                continue;
            }
            Cara::Simpan => {
                let j = s[t - 1];
                let kode = match j { Jenis::Bulat => 1, Jenis::Bool => 2, Jenis::Kosong => 3, Jenis::Pecahan => 5, _ => 4 };
                let v = if matches!(kode, 1 | 2 | 5) { b.use_var(var[t - 1]) } else { i64c(&mut b, 0) };
                let args = [
                    i64c(&mut b, a as i64), i64c(&mut b, t as i64 - 1), v,
                    b.ins().iconst(types::I32, kode), b.ins().iconst(types::I32, (ins.op == OpCode::SimpanBuang) as i64),
                ];
                b.ins().call(f_simpan, &args);
                continue;
            }
            Cara::Buang => {
                let p = i64c(&mut b, t as i64 - 1);
                b.ins().call(f_buang, &[p]);
                continue;
            }
            Cara::Benar => {
                let p = i64c(&mut b, t as i64 - 1);
                let simpan = matches!(ins.op, OpCode::JumpFalseKeep | OpCode::JumpTrueKeep);
                let lepas = b.ins().iconst(types::I32, (!simpan) as i64);
                let c = b.ins().call(f_benar, &[p, lepas]);
                let c = b.inst_results(c)[0];
                let v = b.ins().uextend(types::I64, c);
                if ins.op == OpCode::KeBool { b.def_var(var[t - 1], v); continue; }
                let (sesudah, sasaran) = (blok[ip + 1].expect("sesudah cabang"), blok[a].expect("sasaran cabang"));
                let (ya, tidak) = if matches!(ins.op, OpCode::JumpFalse | OpCode::JumpFalseKeep) {
                    (sesudah, sasaran)
                } else { (sasaran, sesudah) };
                b.ins().brif(v, ya, &[], tidak, &[]);
                terbuka = false;
                continue;
            }
            Cara::Pola => {
                // Gagal (2) = deopt di sini dengan stack sebelum instruksinya; VM yang melapor.
                let (p, d) = (i64c(&mut b, t as i64 - 1), i64c(&mut b, &f.chunk.constants[a] as *const _ as i64));
                let c = b.ins().call(f_pola, &[p, d]);
                let c = b.inst_results(c)[0];
                let salah = b.ins().icmp_imm_u(IntCC::Equal, c, 2);
                jaga(&mut b, &k, &var, salah, ip, s);
                let v = b.ins().uextend(types::I64, c);
                b.def_var(var[t - 1], v);
                continue;
            }
            Cara::Cabang { tumpah, hasil_bool, tujuan } => {
                tumpahkan(&mut b, &var, s, t - tumpah..t, slot, ptr, f_taruh, &r.callee_nilai);
                let args = [
                    i64c(&mut b, ip as i64), i64c(&mut b, s.as_ptr() as i64), i64c(&mut b, t as i64),
                    i64c(&mut b, *tumpah as i64), b.ins().stack_addr(ptr, slot, 0), i64c(&mut b, *hasil_bool as i64),
                ];
                let c = b.ins().call(f_cabang, &args);
                let h = b.inst_results(c)[0];
                let (gagal, terus) = (b.create_block(), b.create_block());
                b.set_cold_block(gagal);
                let salah = b.ins().icmp_imm_s(IntCC::SignedLessThan, h, 0);
                b.ins().brif(salah, gagal, &[], terus, &[]);
                b.switch_to_block(gagal);
                kembali_status(&mut b, GAGAL);
                b.switch_to_block(terus);
                let (ya, tidak) = (blok[tujuan[0]].expect("tujuan cabang"), blok[tujuan[1]].expect("tujuan cabang"));
                let pilih = if *hasil_bool { h } else { b.ins().icmp_imm_s(IntCC::Equal, h, tujuan[0] as i64) };
                b.ins().brif(pilih, ya, &[], tidak, &[]);
                terbuka = false;
                continue;
            }
            Cara::Geser => {
                // Yang dibuang dilepas dari stack VM; puncak milik VM dipindah, yang native cukup variabelnya.
                let d0 = t - a - 1;
                for p in d0..t - 1 {
                    if !s[p].di_vm() { continue; }
                    let pv = i64c(&mut b, p as i64);
                    b.ins().call(f_buang, &[pv]);
                }
                if s[t - 1].di_vm() {
                    let (dari, ke) = (i64c(&mut b, t as i64 - 1), i64c(&mut b, d0 as i64));
                    b.ins().call(f_pindah, &[dari, ke]);
                } else {
                    let v = b.use_var(var[t - 1]);
                    b.def_var(var[d0], v);
                }
                continue;
            }
            Cara::MuatGlobal => {
                let nama = i64c(&mut b, &f.chunk.names[a] as *const String as i64);
                let ke = i64c(&mut b, t as i64);
                let c = b.ins().call(f_muat_global, &[nama, ke]);
                let c = b.inst_results(c)[0];
                jaga(&mut b, &k, &var, c, ip, s);
                if let Some(j) = r.spek[ip] { buka_hasil(&mut b, &k, &var, r, f_buka, wadah, ip + 1, t, j); }
                continue;
            }
            Cara::SimpanGlobal => {
                let j = s[t - 1];
                let kode = match j { Jenis::Bulat => 1, Jenis::Bool => 2, Jenis::Kosong => 3, Jenis::Pecahan => 5, _ => 4 };
                let v = if matches!(kode, 1 | 2 | 5) { b.use_var(var[t - 1]) } else { i64c(&mut b, 0) };
                let args = [
                    i64c(&mut b, &f.chunk.names[a] as *const String as i64), i64c(&mut b, t as i64 - 1), v,
                    b.ins().iconst(types::I32, kode),
                ];
                let c = b.ins().call(f_simpan_global, &args);
                let c = b.inst_results(c)[0];
                jaga(&mut b, &k, &var, c, ip, s);
                continue;
            }
            Cara::Indeks => {
                let j = s[t - 1];
                let kode = match j { Jenis::Bulat => 1, Jenis::Bool => 2, Jenis::Kosong => 3, Jenis::Pecahan => 5, _ => 4 };
                let v = if matches!(kode, 1 | 2 | 5) { b.use_var(var[t - 1]) } else { i64c(&mut b, 0) };
                let (p, kv) = (i64c(&mut b, t as i64 - 2), b.ins().iconst(types::I32, kode));
                let c = b.ins().call(f_indeks, &[p, v, kv]);
                let c = b.inst_results(c)[0];
                jaga(&mut b, &k, &var, c, ip, s);
                // Indeks milik VM di atasnya sudah tidak dipakai.
                if j.di_vm() { let q = i64c(&mut b, t as i64 - 1); b.ins().call(f_buang, &[q]); }
                if let Some(j) = r.spek[ip] { buka_hasil(&mut b, &k, &var, r, f_buka, wadah, ip + 1, t - 2, j); }
                continue;
            }
            Cara::Field => {
                let p = i64c(&mut b, t as i64 - 1);
                let nama = i64c(&mut b, &f.chunk.names[a] as *const String as i64);
                let privat = b.ins().iconst(types::I32, (ins.op == OpCode::GetFieldPrivat) as i64);
                let c = b.ins().call(f_field, &[p, nama, privat]);
                let c = b.inst_results(c)[0];
                jaga(&mut b, &k, &var, c, ip, s);
                if let Some(j) = r.spek[ip] { buka_hasil(&mut b, &k, &var, r, f_buka, wadah, ip + 1, t - 1, j); }
                continue;
            }
            Cara::Langsung(n) => {
                // Bingkai VM callee didorong `masuk`; kode callee dipanggil langsung; `keluar` menaruh hasilnya.
                let jenis = &r.langsung[*n].1;
                tumpahkan(&mut b, &var, s, t - a - 1..t, slot, ptr, f_taruh, &r.callee_nilai);
                let args = [
                    i64c(&mut b, ip as i64), i64c(&mut b, s.as_ptr() as i64), i64c(&mut b, t as i64),
                    i64c(&mut b, a as i64), b.ins().stack_addr(ptr, slot, 0),
                ];
                let c = b.ins().call(f_masuk, &args);
                let m0 = b.inst_results(c)[0];
                let (gagal, cek, asli, akhir) = (b.create_block(), b.create_block(), b.create_block(), b.create_block());
                b.set_cold_block(gagal);
                b.append_block_param(akhir, types::I32);
                let galat = b.ins().icmp_imm_u(IntCC::Equal, m0, 2);
                b.ins().brif(galat, gagal, &[], cek, &[]);
                b.switch_to_block(cek);
                let ulang = b.ins().iconst(types::I32, ULANG);
                b.ins().brif(m0, akhir, &[ulang.into()], asli, &[]);
                b.switch_to_block(asli);
                let argv = b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, (a.max(1) * 8) as u32, 3));
                for (k2, j) in jenis.iter().enumerate() {
                    if !matches!(j, Jenis::Bulat | Jenis::Bool | Jenis::Pecahan) { continue; }
                    let v = b.use_var(var[t - a + k2]);
                    b.ins().stack_store(ptr, v, argv, (k2 * 8) as i32);
                }
                let fref = m.declare_func_in_func(id_langsung[*n], b.func);
                let (pa, ph) = (b.ins().stack_addr(ptr, argv, 0), b.ins().stack_addr(ptr, wadah, 0));
                let c = b.ins().call(fref, &[pa, kedalaman1, ph]);
                let st = b.inst_results(c)[0];
                b.ins().jump(akhir, &[st.into()]);
                b.switch_to_block(gagal);
                kembali_status(&mut b, GAGAL);
                b.switch_to_block(akhir);
                let st = b.block_params(akhir)[0];
                let st = b.ins().sextend(types::I64, st);
                let h = b.ins().stack_load(ptr, types::I64, wadah, 0);
                let c = b.ins().call(f_keluar, &[st, h]);
                let r0 = b.inst_results(c)[0];
                let (gagal2, terus) = (b.create_block(), b.create_block());
                b.set_cold_block(gagal2);
                b.ins().brif(r0, gagal2, &[], terus, &[]);
                b.switch_to_block(gagal2);
                kembali_status(&mut b, GAGAL);
                b.switch_to_block(terus);
                if let Some(j) = r.spek[ip] { buka_hasil(&mut b, &k, &var, r, f_buka, wadah, ip + 1, t - a - 1, j); }
                continue;
            }
            Cara::Bawaan => {
                tumpahkan(&mut b, &var, s, t - a..t, slot, ptr, f_taruh, &r.callee_nilai);
                let args = [
                    i64c(&mut b, ip as i64), i64c(&mut b, s.as_ptr() as i64), i64c(&mut b, t as i64),
                    i64c(&mut b, a as i64), b.ins().stack_addr(ptr, slot, 0),
                ];
                let c = b.ins().call(f_bawaan, &args);
                let st = b.inst_results(c)[0];
                let (gagal, terus) = (b.create_block(), b.create_block());
                b.set_cold_block(gagal);
                b.ins().brif(st, gagal, &[], terus, &[]);
                b.switch_to_block(gagal);
                kembali_status(&mut b, GAGAL);
                b.switch_to_block(terus);
                if let Some(j) = r.spek[ip] { buka_hasil(&mut b, &k, &var, r, f_buka, wadah, ip + 1, t - a - 1, j); }
                continue;
            }
            Cara::Biner => {
                tumpahkan(&mut b, &var, s, t - 2..t, slot, ptr, f_taruh, &r.callee_nilai);
                let args = [i64c(&mut b, ip as i64), i64c(&mut b, s.as_ptr() as i64), i64c(&mut b, t as i64), b.ins().stack_addr(ptr, slot, 0)];
                let c = b.ins().call(f_biner, &args);
                let st = b.inst_results(c)[0];
                let (gagal, terus) = (b.create_block(), b.create_block());
                b.set_cold_block(gagal);
                let salah = b.ins().icmp_imm_u(IntCC::Equal, st, 2);
                b.ins().brif(salah, gagal, &[], terus, &[]);
                b.switch_to_block(gagal);
                kembali_status(&mut b, GAGAL);
                b.switch_to_block(terus);
                if !matches!(ins.op, OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Div | OpCode::Mod | OpCode::Pow) {
                    let v = b.ins().uextend(types::I64, st);
                    b.def_var(var[t - 2], v);
                }
                continue;
            }
            Cara::MuatUpval => {
                let (idx, ke) = (i64c(&mut b, a as i64), i64c(&mut b, t as i64));
                let c = b.ins().call(f_muat_upval, &[idx, ke]);
                let c = b.inst_results(c)[0];
                jaga(&mut b, &k, &var, c, ip, s);
                if let Some(j) = r.spek[ip] { buka_hasil(&mut b, &k, &var, r, f_buka, wadah, ip + 1, t, j); }
                continue;
            }
            Cara::SimpanUpval => {
                let j = s[t - 1];
                let kode = match j { Jenis::Bulat => 1, Jenis::Bool => 2, Jenis::Kosong => 3, Jenis::Pecahan => 5, _ => 4 };
                let v = if matches!(kode, 1 | 2 | 5) { b.use_var(var[t - 1]) } else { i64c(&mut b, 0) };
                let args = [i64c(&mut b, a as i64), i64c(&mut b, t as i64 - 1), v, b.ins().iconst(types::I32, kode)];
                let c = b.ins().call(f_simpan_upval, &args);
                let c = b.inst_results(c)[0];
                jaga(&mut b, &k, &var, c, ip, s);
                continue;
            }
            Cara::Salin => {
                let (dari, ke) = (i64c(&mut b, t as i64 - 1), i64c(&mut b, t as i64));
                b.ins().call(f_salin, &[dari, ke]);
                continue;
            }
            Cara::Tukar => {
                // Isi native ikut variabelnya; isi milik VM ikut posisinya di stack VM.
                let (x, y) = (t - 2, t - 1);
                let (px, py) = (i64c(&mut b, x as i64), i64c(&mut b, y as i64));
                match (s[x].di_vm(), s[y].di_vm()) {
                    (true, true) => { b.ins().call(f_tukar, &[px, py]); }
                    (true, false) => { b.ins().call(f_pindah, &[px, py]); let v = b.use_var(var[y]); b.def_var(var[x], v); }
                    _ => { b.ins().call(f_pindah, &[py, px]); let v = b.use_var(var[x]); b.def_var(var[y], v); }
                }
                continue;
            }
            Cara::Metode(n) => {
                let (p, l) = (i64c(&mut b, t as i64 - 1), i64c(&mut b, &r.metode[*n] as *const String as i64));
                let c = b.ins().call(f_cek_metode, &[p, l]);
                let c = b.inst_results(c)[0];
                jaga_spek(&mut b, &k, &var, c, ip, s);
                continue;
            }
            Cara::Sebar => {
                // 1 = `Err`/`None`: fungsinya kembali dengan nilai itu (masuk dari VM), selain itu VM yang menjalankannya.
                let p = i64c(&mut b, t as i64 - 1);
                let c = b.ins().call(f_sebar, &[p]);
                let c = b.inst_results(c)[0];
                if r.kembali == super::layak::KEMBALI_SKALAR && !r.ada_defer {
                    let (pulang, terus) = (b.create_block(), b.create_block());
                    let satu = b.ins().icmp_imm_u(IntCC::Equal, c, 1);
                    b.ins().brif(satu, pulang, &[], terus, &[]);
                    b.switch_to_block(pulang);
                    b.ins().store(fl, p, keluar, 0);
                    kembali_status(&mut b, BERHASIL_NILAI);
                    b.switch_to_block(terus);
                }
                jaga(&mut b, &k, &var, c, ip, s);
                continue;
            }
            Cara::IterAda => {
                // Gagal (2) = deopt di sini; VM yang melaporkan state iterator yang rusak.
                let p = i64c(&mut b, a as i64);
                let c = b.ins().call(f_iter_ada, &[p]);
                let c = b.inst_results(c)[0];
                let salah = b.ins().icmp_imm_u(IntCC::Equal, c, 2);
                jaga(&mut b, &k, &var, salah, ip, s);
                let v = b.ins().uextend(types::I64, c);
                b.def_var(var[t], v);
                continue;
            }
            Cara::Maju => {
                let p = i64c(&mut b, a as i64);
                let c = b.ins().call(f_maju, &[p]);
                let c = b.inst_results(c)[0];
                jaga(&mut b, &k, &var, c, ip, s);
                continue;
            }
            Cara::Payload => {
                let p = i64c(&mut b, t as i64 - 1);
                let c = b.ins().call(f_payload, &[p]);
                let c = b.inst_results(c)[0];
                jaga(&mut b, &k, &var, c, ip, s);
                if let Some(j) = r.spek[ip] { buka_hasil(&mut b, &k, &var, r, f_buka, wadah, ip + 1, t - 1, j); }
                continue;
            }
            Cara::KembaliNilai => {
                let p = i64c(&mut b, t as i64 - 1);
                b.ins().store(fl, p, keluar, 0);
                kembali_status(&mut b, BERHASIL_NILAI);
                terbuka = false;
                continue;
            }
            Cara::KembaliUnit => {
                kembali_status(&mut b, BERHASIL_UNIT);
                terbuka = false;
                continue;
            }
        };
        match ins.op {
            OpCode::LoadLocal | OpCode::LokalHitung => { let v = b.use_var(var[a]); b.def_var(var[t], v); }
            OpCode::IntImm => { let v = b.ins().iconst(types::I64, ins.arg as i32 as i64); b.def_var(var[t], v); }
            OpCode::Const => { let v = b.ins().iconst(types::I64, r.konstanta[ip].unwrap_or(0)); b.def_var(var[t], v); }
            OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Div if s[t - 1] == Jenis::Pecahan || s[t - 2] == Jenis::Pecahan => {
                let x = atas(&mut b, 2);
                let x = ke_f64(&mut b, x, s[t - 2]);
                let y = atas(&mut b, 1);
                let y = ke_f64(&mut b, y, s[t - 1]);
                let h = match ins.op {
                    OpCode::Add => b.ins().fadd(x, y),
                    OpCode::Sub => b.ins().fsub(x, y),
                    OpCode::Mul => b.ins().fmul(x, y),
                    _ => b.ins().fdiv(x, y),
                };
                let h = dari_f64(&mut b, h);
                b.def_var(var[t - 2], h);
            }
            OpCode::Add | OpCode::Sub | OpCode::Mul => {
                let (x, y) = (atas(&mut b, 2), atas(&mut b, 1));
                let (h, luap) = match ins.op {
                    OpCode::Add => b.ins().sadd_overflow(x, y),
                    OpCode::Sub => b.ins().ssub_overflow(x, y),
                    _ => b.ins().smul_overflow(x, y),
                };
                jaga(&mut b, &k, &var, luap, ip, s);
                b.def_var(var[t - 2], h);
            }
            OpCode::Mod | OpCode::Div => {
                let (x, y) = (atas(&mut b, 2), atas(&mut b, 1));
                // Pembagi 0 dan -1 jatuh ke VM: kalimat galatnya, luapan `MIN / -1`, dan aturan `int_biner`.
                let nol = b.ins().icmp_imm_s(IntCC::Equal, y, 0);
                let min1 = b.ins().icmp_imm_s(IntCC::Equal, y, -1);
                let tolak = b.ins().bor(nol, min1);
                jaga(&mut b, &k, &var, tolak, ip, s);
                let h = if ins.op == OpCode::Mod { b.ins().srem(x, y) } else { b.ins().sdiv(x, y) };
                b.def_var(var[t - 2], h);
            }
            OpCode::Lt | OpCode::Le | OpCode::Gt | OpCode::Ge | OpCode::Eq | OpCode::Ne
                if s[t - 1] == Jenis::Pecahan || s[t - 2] == Jenis::Pecahan => {
                // Urutan: NaN membuat keempatnya `false`; `!=` benar untuk NaN (`!vm_eq`).
                let cc = match ins.op {
                    OpCode::Lt => FloatCC::LessThan,
                    OpCode::Le => FloatCC::LessThanOrEqual,
                    OpCode::Gt => FloatCC::GreaterThan,
                    OpCode::Ge => FloatCC::GreaterThanOrEqual,
                    OpCode::Eq => FloatCC::Equal,
                    _ => FloatCC::NotEqual,
                };
                let x = atas(&mut b, 2);
                let x = ke_f64(&mut b, x, s[t - 2]);
                let y = atas(&mut b, 1);
                let y = ke_f64(&mut b, y, s[t - 1]);
                let c = b.ins().fcmp(cc, x, y);
                let v = b.ins().uextend(types::I64, c);
                b.def_var(var[t - 2], v);
            }
            OpCode::Lt | OpCode::Le | OpCode::Gt | OpCode::Ge | OpCode::Eq | OpCode::Ne => {
                let cc = match ins.op {
                    OpCode::Lt => IntCC::SignedLessThan,
                    OpCode::Le => IntCC::SignedLessThanOrEqual,
                    OpCode::Gt => IntCC::SignedGreaterThan,
                    OpCode::Ge => IntCC::SignedGreaterThanOrEqual,
                    OpCode::Eq => IntCC::Equal,
                    _ => IntCC::NotEqual,
                };
                let (x, y) = (atas(&mut b, 2), atas(&mut b, 1));
                let c = b.ins().icmp(cc, x, y);
                let v = b.ins().uextend(types::I64, c);
                b.def_var(var[t - 2], v);
            }
            OpCode::BitAnd | OpCode::BitOr | OpCode::BitXor | OpCode::AndNot => {
                let (x, y) = (atas(&mut b, 2), atas(&mut b, 1));
                let h = match ins.op {
                    OpCode::BitAnd => b.ins().band(x, y),
                    OpCode::BitOr => b.ins().bor(x, y),
                    OpCode::BitXor => b.ins().bxor(x, y),
                    _ => b.ins().band_not(x, y),
                };
                b.def_var(var[t - 2], h);
            }
            OpCode::BitNot => { let x = atas(&mut b, 1); let h = b.ins().bnot(x); b.def_var(var[t - 1], h); }
            // Geser kiri cuma kalau hasil i128-nya muat di 64 bit (bisa digeser balik); sisanya VM.
            OpCode::Shl => {
                let (x, y) = (atas(&mut b, 2), atas(&mut b, 1));
                let jauh = b.ins().icmp_imm_u(IntCC::UnsignedGreaterThan, y, 63);
                jaga(&mut b, &k, &var, jauh, ip, s);
                let h = b.ins().ishl(x, y);
                let balik = b.ins().sshr(h, y);
                let hilang = b.ins().icmp(IntCC::NotEqual, balik, x);
                jaga(&mut b, &k, &var, hilang, ip, s);
                b.def_var(var[t - 2], h);
            }
            // Geser kanan atas nilai 64 bit: di atas 63 cuma tinggal tandanya; negatif dan >= 128 ke VM.
            OpCode::Shr => {
                let (x, y) = (atas(&mut b, 2), atas(&mut b, 1));
                let salah = b.ins().icmp_imm_u(IntCC::UnsignedGreaterThanOrEqual, y, 128);
                jaga(&mut b, &k, &var, salah, ip, s);
                let enam3 = b.ins().iconst(types::I64, 63);
                let besar = b.ins().icmp_imm_u(IntCC::UnsignedGreaterThan, y, 63);
                let kk = b.ins().select(besar, enam3, y);
                let h = b.ins().sshr(x, kk);
                b.def_var(var[t - 2], h);
            }
            OpCode::AmbilLokal => { let v = b.use_var(var[a]); b.def_var(var[t], v); }
            OpCode::IndeksLokal => {
                let (rel, i) = (b.ins().iconst(types::I64, a as i64), atas(&mut b, 1));
                let pk = b.ins().stack_addr(ptr, wadah, 0);
                let c = b.ins().call(baca, &[rel, i, pk]);
                let st = b.inst_results(c)[0];
                jaga_spek(&mut b, &k, &var, st, ip, s);
                let v = b.ins().stack_load(ptr, types::I64, wadah, 0);
                b.def_var(var[t - 1], v);
            }
            OpCode::TulisIndexLokal => {
                let (v, i) = (atas(&mut b, 2), atas(&mut b, 1));
                let rel = b.ins().iconst(types::I64, a as i64);
                let jenis = b.ins().iconst(types::I32, match s[t - 2] { Jenis::Bool => 2, Jenis::Pecahan => 5, _ => 1 });
                let c = b.ins().call(tulis, &[rel, i, v, jenis]);
                let st = b.inst_results(c)[0];
                jaga_spek(&mut b, &k, &var, st, ip, s);
            }
            OpCode::True | OpCode::False => {
                let v = b.ins().iconst(types::I64, (ins.op == OpCode::True) as i64);
                b.def_var(var[t], v);
            }
            OpCode::Nil => {}
            OpCode::Neg if s[t - 1] == Jenis::Pecahan => {
                let x = atas(&mut b, 1);
                let x = ke_f64(&mut b, x, Jenis::Pecahan);
                let h = b.ins().fneg(x);
                let h = dari_f64(&mut b, h);
                b.def_var(var[t - 1], h);
            }
            OpCode::Neg => {
                let x = atas(&mut b, 1);
                // -MIN tidak muat 64 bit: VM menghitungnya di 128 bit.
                let luap = b.ins().icmp_imm_s(IntCC::Equal, x, i64::MIN);
                jaga(&mut b, &k, &var, luap, ip, s);
                let h = b.ins().ineg(x);
                b.def_var(var[t - 1], h);
            }
            OpCode::Not => { let x = atas(&mut b, 1); let h = b.ins().bxor_imm_s(x, 1); b.def_var(var[t - 1], h); }
            OpCode::KeBool => {
                let x = atas(&mut b, 1);
                let c = b.ins().icmp_imm_s(IntCC::NotEqual, x, 0);
                let h = b.ins().uextend(types::I64, c);
                b.def_var(var[t - 1], h);
            }
            OpCode::Dup => { let v = atas(&mut b, 1); b.def_var(var[t], v); }
            OpCode::Swap => {
                let (x, y) = (atas(&mut b, 2), atas(&mut b, 1));
                b.def_var(var[t - 2], y);
                b.def_var(var[t - 1], x);
            }
            OpCode::SlideDown => { let v = atas(&mut b, 1); b.def_var(var[t - a - 1], v); }
            OpCode::Pop | OpCode::LoadGlobal | OpCode::PeriksaArgMetode => {}
            OpCode::StoreLocal | OpCode::SimpanBuang => { let v = atas(&mut b, 1); b.def_var(var[a], v); }
            OpCode::Jump => { b.ins().jump(blok[a].expect("sasaran lompat terjangkau"), &[]); terbuka = false; }
            OpCode::JumpFalse | OpCode::JumpTrue | OpCode::JumpFalseKeep | OpCode::JumpTrueKeep => {
                let c = atas(&mut b, 1);
                let (sesudah, sasaran) = (blok[ip + 1].expect("sesudah cabang"), blok[a].expect("sasaran cabang"));
                let (ya, tidak) = if matches!(ins.op, OpCode::JumpFalse | OpCode::JumpFalseKeep) {
                    (sesudah, sasaran)
                } else { (sasaran, sesudah) };
                b.ins().brif(c, ya, &[], tidak, &[]);
                terbuka = false;
            }
            OpCode::MakeIterRentang => {
                let (lo, hi) = (atas(&mut b, 2), atas(&mut b, 1));
                // Aturan `range_hitung` untuk langkah 1; selisih yang tak muat 64 bit dihitung VM.
                let (d, luap) = b.ins().ssub_overflow(hi, lo);
                jaga(&mut b, &k, &var, luap, ip, s);
                let (jumlah, ada) = if a == 1 {
                    let satu = b.ins().iconst(types::I64, 1);
                    let (d1, luap) = b.ins().sadd_overflow(d, satu);
                    jaga(&mut b, &k, &var, luap, ip, s);
                    (d1, b.ins().icmp(IntCC::SignedLessThanOrEqual, lo, hi))
                } else { (d, b.ins().icmp(IntCC::SignedLessThan, lo, hi)) };
                let nol = b.ins().iconst(types::I64, 0);
                let jumlah = b.ins().select(ada, jumlah, nol);
                b.def_var(var[t - 2], jumlah);
                b.def_var(var[t - 1], lo);
                b.def_var(var[t], nol);
            }
            OpCode::IterAda => {
                let (jumlah, idx) = (b.use_var(var[a]), b.use_var(var[a + 2]));
                let c = b.ins().icmp(IntCC::SignedLessThan, idx, jumlah);
                let v = b.ins().uextend(types::I64, c);
                b.def_var(var[t], v);
            }
            OpCode::IterMaju => {
                let x = b.use_var(var[a]);
                let luap = b.ins().icmp_imm_s(IntCC::Equal, x, i64::MAX);
                jaga(&mut b, &k, &var, luap, ip, s);
                let h = b.ins().iadd_imm_s(x, 1);
                b.def_var(var[a], h);
            }
            OpCode::IterVar => {
                let kk = a / 2;
                let idx = b.use_var(var[kk + 2]);
                let v = if a % 2 == 0 { idx } else {
                    let awal = b.use_var(var[kk + 1]);
                    let (h, luap) = b.ins().sadd_overflow(awal, idx);
                    jaga(&mut b, &k, &var, luap, ip, s);
                    h
                };
                b.def_var(var[t], v);
            }
            OpCode::Return => {
                let v = atas(&mut b, 1);
                b.ins().store(fl, v, keluar, 0);
                let st = match s[t - 1] { Jenis::Bool => BERHASIL_BOOL, Jenis::Pecahan => BERHASIL_PECAHAN, _ => BERHASIL };
                let st = b.ins().iconst(types::I32, st);
                b.ins().return_(&[st]);
                terbuka = false;
            }
            OpCode::Call => {
                let Jenis::Fungsi(i) = s[t - a - 1] else { unreachable!("dijamin layak.rs") };
                let fref = m.declare_func_in_func(id_callee[i].expect("callee asli dikompilasi"), b.func);
                let slot = b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, (a.max(1) * 8) as u32, 3));
                let hasil = b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 3));
                for k in 0..a {
                    let v = b.use_var(var[t - a + k]);
                    b.ins().stack_store(ptr, v, slot, (k * 8) as i32);
                }
                let pa = b.ins().stack_addr(ptr, slot, 0);
                let ph = b.ins().stack_addr(ptr, hasil, 0);
                let panggil = b.ins().call(fref, &[pa, kedalaman1, ph]);
                let st = b.inst_results(panggil)[0];
                let terus = b.create_block();
                let gagal = b.create_block();
                b.set_cold_block(gagal);
                b.ins().brif(st, gagal, &[], terus, &[]);
                b.switch_to_block(gagal);
                // Callee belum mulai: VM menjalankan `Call` ini sendiri. Callee sudah tercatat: lanjut sesudahnya.
                let ulang = b.ins().icmp_imm_s(IntCC::Equal, st, ULANG);
                let (bu, bb) = (b.create_block(), b.create_block());
                b.set_cold_block(bu);
                b.set_cold_block(bb);
                b.ins().brif(ulang, bu, &[], bb, &[]);
                b.switch_to_block(bu);
                keluar_deopt(&mut b, &k, &var, ip, s);
                b.switch_to_block(bb);
                keluar_deopt(&mut b, &k, &var, ip + 1, &s[..t - a - 1]);
                b.switch_to_block(terus);
                let v = b.ins().stack_load(ptr, types::I64, hasil, 0);
                b.def_var(var[t - a - 1], v);
            }
            _ => unreachable!("dijamin layak.rs"),
        }
    }
    b.switch_to_block(dalam);
    let st = b.ins().iconst(types::I32, ULANG);
    b.ins().return_(&[st]);
    b.seal_all_blocks();
    b.finalize(m.target_config());
}
