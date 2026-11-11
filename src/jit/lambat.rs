//! Jalur lambat J4 (`dokumentasi/jit/j4-rencana.md`): kode native membaca dan menulis nilai milik VM
//! (`Jenis::Nilai`) lewat fungsi di sini, dengan aturan VM yang sama. Gagal (status 1) = belum dikerjakan
//! apa pun yang terlihat, jadi kode native deopt di instruksi itu dan VM yang menjalankannya.

use std::cell::{Cell, RefCell};

use super::layak::Jenis;
use crate::vm::opcode::OpCode;
use crate::vm::value::VmValue;
use crate::vm::vm::{Vm, VmError};

thread_local! {
    /// VM dan basis bingkai terluar yang sedang dijalankan kode native di thread ini.
    static KONTEKS: Cell<(*mut Vm, usize)> = const { Cell::new((std::ptr::null_mut(), 0)) };
    /// Panggilan langsung yang sedang berjalan (`masuk`/`keluar`): kedalaman bingkai pemanggil, basisnya,
    /// dan posisi mutlak slot fungsi callee.
    static LANGSUNG: RefCell<Vec<(usize, usize, usize)>> = const { RefCell::new(Vec::new()) };
    /// Galat dari instruksi yang dijalankan `langkah`; diambil `panggil::jalankan`.
    static GALAT: RefCell<Option<VmError>> = const { RefCell::new(None) };
}

/// Galat `langkah` terakhir di thread ini (status `GAGAL` kode native).
pub(crate) fn ambil_galat() -> VmError {
    GALAT.with(|g| g.borrow_mut().take()).unwrap_or_else(|| VmError::new("bug di jrgc: galat jalur lambat JIT hilang"))
}

/// VM dan basis bingkai terluar. Kode native berjalan di dalam `panggil::jalankan`, yang tidak
/// menyentuh VM sampai kode itu kembali.
fn konteks() -> (&'static mut Vm, usize) {
    let (vm, basis) = KONTEKS.with(|k| k.get());
    assert!(!vm.is_null(), "bug di jrgc: jalur lambat JIT tanpa VM");
    (unsafe { &mut *vm }, basis)
}

/// Posisi `p` bingkai terluar ada di stack VM (yang lebih pendek diisi `nil`).
fn sediakan(vm: &mut Vm, basis: usize, p: usize) -> &mut VmValue {
    let i = basis + p;
    // Posisi baru di puncak (yang paling sering): satu `push`, bukan `resize`.
    if vm.stack.len() == i { vm.stack.push(VmValue::Nil); } else if vm.stack.len() < i { vm.stack.resize(i + 1, VmValue::Nil); }
    &mut vm.stack[i]
}

fn nilai_skalar(j: Jenis, v: i64) -> Option<VmValue> {
    match j {
        Jenis::Bulat => Some(VmValue::Int(v as i128)),
        Jenis::Bool => Some(VmValue::Bool(v != 0)),
        Jenis::Pecahan => Some(VmValue::Float(f64::from_bits(v as u64))),
        Jenis::Kosong => Some(VmValue::Nil),
        _ => None,
    }
}

/// VM menjalankan instruksi `ip` bingkai terluar. Stack VM dipotong ke `t` posisi dan `tumpah` posisi
/// teratas diisi dari `nilai` (posisi `Nilai` sudah di sana). `Some(sesudah)`: tinggi yang diharapkan,
/// juga untuk melengkapi `ReturnNil` bersarang. Hasilnya kedalaman bingkai; galat disimpan (`ambil_galat`).
fn satu(ip: i64, jenis: *const Jenis, t: i64, tumpah: i64, sesudah: Option<usize>, nilai: *const i64) -> Option<usize> {
    let (vm, basis) = konteks();
    let (t, ambil) = (t as usize, tumpah as usize);
    // Tabel jenis milik `Rencana` dan slot nilai bingkai native, masing-masing `t` posisi.
    let (jenis, nilai) = unsafe { (std::slice::from_raw_parts(jenis, t), std::slice::from_raw_parts(nilai, t)) };
    // Yang di atas `t` sudah dibuang kode native: dilepas di sini, sebelum ada yang menghitung pemegangnya.
    vm.stack.truncate(basis + t);
    while vm.stack.len() < basis + t { vm.stack.push(VmValue::Nil); }
    for i in t - ambil..t {
        if let Some(v) = nilai_skalar(jenis[i], nilai[i]) { vm.stack[basis + i] = v; }
    }
    let d = vm.frames.len();
    // Opcode yang badannya fungsi `Vm` sendiri dijalankan langsung, tanpa masuk loop dispatch.
    let fr = vm.frames.last_mut().expect("bingkai terluar");
    let ins = fr.func.chunk.code[ip as usize];
    let sp = if ins.span == 0 { None } else { fr.func.chunk.spans.get(ins.span as usize).copied() };
    fr.ip = ip as usize + 1;
    let pertama = match ins.op {
        OpCode::Call => vm.call_value_at(ins.arg as usize, sp, true),
        OpCode::GetMethod => vm.op_get_method(ins.arg, sp),
        OpCode::PeriksaArgMetode => vm.op_periksa_arg_metode(ins.arg, sp),
        OpCode::BuildStruct => vm.op_build_struct(ins.arg, sp),
        OpCode::BuildArray | OpCode::BuildTuple => { vm.op_build_larik(ins.arg, ins.op == OpCode::BuildTuple); Ok(()) }
        OpCode::SetIndex => vm.op_set_index(sp),
        OpCode::Typeof => vm.op_typeof(sp),
        OpCode::Len => vm.op_len(sp),
        OpCode::CopyVal => vm.op_copy_val(sp),
        OpCode::Dup => { let v = vm.stack[vm.stack.len() - 1].clone(); vm.stack.push(v); Ok(()) }
        OpCode::Swap => { let n = vm.stack.len(); vm.stack.swap(n - 1, n - 2); Ok(()) }
        _ => {
            vm.frames[d - 1].ip = ip as usize;
            vm.run_until_inner::<true, true>(d - 1)
        }
    };
    // `Call` atas fungsi VM mendorong bingkai: badannya dijalankan sampai kembali ke bingkai ini.
    // `ReturnNil` yang kembali tepat ke kedalaman itu tidak mendorong apa pun: jawabannya `unit`
    // (aturan `Vm::call_value_immediate`).
    let hasil = pertama.and_then(|_| {
        if vm.frames.len() <= d { return Ok(()); }
        vm.run_until_inner::<true, false>(d)?;
        if vm.frames.len() == d && sesudah.is_some_and(|n| vm.stack.len() + 1 == basis + n) { vm.stack.push(VmValue::Unit); }
        Ok(())
    });
    if let Err(e) = hasil {
        GALAT.with(|g| *g.borrow_mut() = Some(e));
        return None;
    }
    let ok = vm.frames.len() == d && sesudah.is_none_or(|n| vm.frames[d - 1].ip == ip as usize + 1 && vm.stack.len() == basis + n);
    assert!(ok, "bug di jrgc: langkah JIT {:?} di ip {ip} meninggalkan VM dalam bentuk lain (bingkai {}/{d}, ip {}, stack {}/{:?})",
        vm.frames.last().map(|f| f.func.chunk.code[ip as usize].op), vm.frames.len(), vm.frames.last().map_or(0, |f| f.ip),
        vm.stack.len(), sesudah.map(|n| basis + n));
    Some(d)
}

/// Satu instruksi yang tidak melompat; sesudahnya tingginya harus `sesudah`. 0 = selesai, 2 = galat.
pub extern "C" fn langkah(ip: i64, jenis: *const Jenis, t: i64, tumpah: i64, sesudah: i64, nilai: *const i64) -> i32 {
    if satu(ip, jenis, t, tumpah, Some(sesudah as usize), nilai).is_some() { 0 } else { 2 }
}

/// Satu instruksi yang bercabang (`Cara::Cabang`): `ambil_bool` = `bool` di puncak diambil dan
/// dikembalikan (0/1), selain itu `ip` berikutnya; -1 = galat.
pub extern "C" fn langkah_cabang(ip: i64, jenis: *const Jenis, t: i64, tumpah: i64, nilai: *const i64, ambil_bool: i64) -> i64 {
    let Some(d) = satu(ip, jenis, t, tumpah, None, nilai) else { return -1 };
    let (vm, _) = konteks();
    if ambil_bool == 0 { return vm.frames[d - 1].ip as i64; }
    match vm.stack.pop() {
        Some(VmValue::Bool(b)) => b as i64,
        lain => panic!("bug di jrgc: langkah cabang JIT di ip {ip} menaruh {lain:?}, bukan bool"),
    }
}

/// Panggilan langsung (`Cara::Langsung`): callee dan `argc` argumennya (posisi `t - argc - 1..t`) ke stack
/// VM, bingkai callee didorong dengan aturan `Vm::call_value`, dan basis konteks jadi milik callee.
/// 0 = jalankan kode native callee; 1 = VM yang menjalankannya; 2 = galat (`ambil_galat`).
pub extern "C" fn masuk(ip: i64, jenis: *const Jenis, t: i64, argc: i64, nilai: *const i64) -> i32 {
    let (vm, basis) = konteks();
    let (t, argc) = (t as usize, argc as usize);
    let jenis = unsafe { std::slice::from_raw_parts(jenis, t) };
    let nilai = unsafe { std::slice::from_raw_parts(nilai, t) };
    vm.stack.truncate(basis + t);
    while vm.stack.len() < basis + t { vm.stack.push(VmValue::Nil); }
    for i in t - argc..t {
        if let Some(v) = nilai_skalar(jenis[i], nilai[i]) { vm.stack[basis + i] = v; }
    }
    let d = vm.frames.len();
    let fr = vm.frames.last_mut().expect("bingkai terluar");
    let sp = fr.func.chunk.code.get(ip as usize).and_then(|i| (i.span != 0).then(|| fr.func.chunk.spans.get(i.span as usize).copied()).flatten());
    fr.ip = ip as usize + 1;
    let slot = basis + t - argc - 1;
    let VmValue::Function(func) = vm.stack[slot].clone() else { panic!("bug di jrgc: panggilan langsung JIT bukan atas fungsi") };
    if let Err(e) = vm.periksa_kedalaman(&func.name, sp) {
        GALAT.with(|g| *g.borrow_mut() = Some(e));
        return 2;
    }
    if let Some(p) = &func.chunk.profil { p.catat_panggilan(); }
    vm.dorong_bingkai(crate::vm::vm::CallFrame { func, ip: 0, slot, defers: Vec::new(), argc: argc as u8, closure: None });
    LANGSUNG.with(|l| l.borrow_mut().push((d, basis, slot)));
    // Rekursi native sedalam itu diteruskan VM (lihat `panggil::jalankan`).
    let ukuran = crate::interpreter::Interpreter::INTERPRETER_STACK_SIZE;
    if crate::interpreter::stack_terpakai().is_some_and(|t| t > ukuran / 2) { return 1; }
    KONTEKS.with(|k| k.set((vm, slot + 1)));
    0
}

/// Akhir panggilan langsung: status kode callee (`turun::BERHASIL`…; `ULANG` juga untuk "VM yang
/// menjalankan"), basis konteks pemanggil dipulihkan, hasilnya di slot fungsi callee. 0 = selesai; 2 = galat.
pub extern "C" fn keluar(st: i64, hasil: i64) -> i32 {
    use super::turun::{BERHASIL, BERHASIL_BOOL, BERHASIL_NILAI, BERHASIL_PECAHAN, BERHASIL_UNIT, DEOPT, GAGAL};
    let (vm, _) = konteks();
    let (d, basis, slot) = LANGSUNG.with(|l| l.borrow_mut().pop()).expect("bug di jrgc: keluar tanpa masuk");
    KONTEKS.with(|k| k.set((vm, basis)));
    let v = match st {
        BERHASIL => VmValue::Int(hasil as i128),
        BERHASIL_BOOL => VmValue::Bool(hasil != 0),
        BERHASIL_PECAHAN => VmValue::Float(f64::from_bits(hasil as u64)),
        BERHASIL_NILAI => std::mem::replace(&mut vm.stack[slot + 1 + hasil as usize], VmValue::Nil),
        BERHASIL_UNIT => VmValue::Unit,
        GAGAL => return 2,
        _ => {
            // Deopt di callee: bingkainya disusun ulang lalu VM menyelesaikannya; `ULANG` = belum mulai.
            if st == DEOPT { super::deopt::pulihkan(vm, super::deopt::ambil()); }
            if let Err(e) = vm.run_until_inner::<true, false>(d) {
                GALAT.with(|g| *g.borrow_mut() = Some(e));
                return 2;
            }
            // `Return` VM menaruh hasilnya di slot; `ReturnNil` tidak menaruh apa pun (`unit`).
            let v = if vm.stack.len() > slot { vm.stack.pop().unwrap_or(VmValue::Unit) } else { VmValue::Unit };
            vm.stack.truncate(slot);
            vm.stack.push(v);
            return 0;
        }
    };
    if let Some(fr) = vm.ambil_bingkai() { vm.stack.truncate(fr.slot); }
    vm.catat_hasil(&v);
    vm.stack.push(v);
    0
}

/// `Call` atas fungsi bawaan di posisi `t - argc - 1` (milik VM): argumennya dari nilai native atau
/// posisi VM (diambil), hasilnya di posisi fungsinya (`Vm::panggil_native`). 0 = selesai, 2 = galat.
pub extern "C" fn bawaan(ip: i64, jenis: *const Jenis, t: i64, argc: i64, nilai: *const i64) -> i32 {
    let (vm, basis) = konteks();
    let (t, argc) = (t as usize, argc as usize);
    let jenis = unsafe { std::slice::from_raw_parts(jenis, t) };
    let nilai = unsafe { std::slice::from_raw_parts(nilai, t) };
    let mut args = Vec::with_capacity(argc);
    for i in t - argc..t {
        args.push(match nilai_skalar(jenis[i], nilai[i]) {
            Some(v) => v,
            None => std::mem::replace(sediakan(vm, basis, i), VmValue::Nil),
        });
    }
    let VmValue::NativeFn(f) = *sediakan(vm, basis, t - argc - 1) else { panic!("bug di jrgc: panggilan bawaan JIT bukan atas fungsi bawaan") };
    let fr = vm.frames.last_mut().expect("bingkai terluar");
    let sp = fr.func.chunk.code.get(ip as usize).and_then(|i| (i.span != 0).then(|| fr.func.chunk.spans.get(i.span as usize).copied()).flatten());
    fr.ip = ip as usize + 1;
    match vm.panggil_native(f, args, sp, true) {
        Ok(v) => {
            vm.catat_hasil(&v);
            *sediakan(vm, basis, t - argc - 1) = v;
            0
        }
        Err(e) => {
            GALAT.with(|g| *g.borrow_mut() = Some(e));
            2
        }
    }
}

/// Aritmetika/banding instruksi `ip` atas posisi `t - 2`, `t - 1` (angka native atau milik VM, diambil),
/// lewat `Vm::op_biner`. Aritmetika: hasilnya di posisi `t - 2`, 0 = selesai. Banding: 0/1. 2 = galat.
pub extern "C" fn biner(ip: i64, jenis: *const Jenis, t: i64, nilai: *const i64) -> i32 {
    let (vm, basis) = konteks();
    let t = t as usize;
    let jenis = unsafe { std::slice::from_raw_parts(jenis, t) };
    let nilai = unsafe { std::slice::from_raw_parts(nilai, t) };
    let mut ambil = |i: usize| nilai_skalar(jenis[i], nilai[i])
        .unwrap_or_else(|| std::mem::replace(sediakan(vm, basis, i), VmValue::Nil));
    let (a, b) = (ambil(t - 2), ambil(t - 1));
    let fr = vm.frames.last_mut().expect("bingkai terluar");
    let ins = fr.func.chunk.code[ip as usize];
    let sp = if ins.span == 0 { None } else { fr.func.chunk.spans.get(ins.span as usize).copied() };
    fr.ip = ip as usize + 1;
    match vm.op_biner(ins.op, a, b, sp) {
        Ok(v) if matches!(ins.op, OpCode::Eq | OpCode::Ne | OpCode::Lt | OpCode::Le | OpCode::Gt | OpCode::Ge) => v.is_truthy() as i32,
        Ok(v) => { *sediakan(vm, basis, t - 2) = v; 0 }
        Err(e) => {
            GALAT.with(|g| *g.borrow_mut() = Some(e));
            2
        }
    }
}

/// `Propagate` (`?`) atas posisi `p`: 0 = `Ok`/`Some`, posisinya jadi payload; 1 = `Err`/`None`, tidak
/// disentuh (fungsinya kembali dengan nilai itu); 2 = bukan `Result`/`Option` (VM yang melapor).
pub extern "C" fn sebar(p: i64) -> i32 {
    let (vm, basis) = konteks();
    let v = sediakan(vm, basis, p as usize);
    match Vm::tagged_parts(v) {
        Some((ty, var, isi)) if ty == "Result" || ty == "Option" => match var.as_str() {
            "Ok" | "Some" => { *v = isi.unwrap_or(VmValue::Nil); 0 }
            "Err" | "None" => 1,
            _ => 2,
        },
        _ => 2,
    }
}

/// `LoadLocal` atas lokal milik VM: posisi `ke` = isi lokal `dari` (sel dibaca isinya).
pub extern "C" fn muat(dari: i64, ke: i64) {
    let (vm, basis) = konteks();
    let v = vm.baca_lokal(basis + dari as usize).unwrap_or(VmValue::Nil);
    *sediakan(vm, basis, ke as usize) = v;
}

/// `Const`/`Unit`: posisi `ke` = salinan konstanta di `k` (milik chunk yang dikompilasi); null = `()`.
pub extern "C" fn taruh(ke: i64, k: *const VmValue) {
    let (vm, basis) = konteks();
    let v = if k.is_null() { VmValue::Unit } else { unsafe { (*k).clone() } };
    *sediakan(vm, basis, ke as usize) = v;
}

/// `AmbilLokal` atas lokal milik VM (`Vm::ambil_lokal`): posisi `ke` = isinya.
pub extern "C" fn ambil(dari: i64, ke: i64) {
    let (vm, basis) = konteks();
    let v = vm.ambil_lokal(basis + dari as usize).unwrap_or(VmValue::Nil);
    *sediakan(vm, basis, ke as usize) = v;
}

/// `StoreLocal` (`pindah` 0) / `SimpanBuang` (1): lokal `ke` = nilai posisi `dari`, berjenis `jenis`
/// (kode `panggil::kode_jenis`; 4 = milik VM, dibaca dari stack-nya).
pub extern "C" fn simpan(ke: i64, dari: i64, nilai: i64, jenis: i32, pindah: i32) {
    let (vm, basis) = konteks();
    let v = match jenis {
        1 => VmValue::Int(nilai as i128),
        2 => VmValue::Bool(nilai != 0),
        3 => VmValue::Nil,
        5 => VmValue::Float(f64::from_bits(nilai as u64)),
        _ => {
            let t = sediakan(vm, basis, dari as usize);
            if pindah != 0 { std::mem::replace(t, VmValue::Nil) } else { t.clone() }
        }
    };
    vm.simpan_lokal(basis + ke as usize, v);
}

/// `CekEnum` atas posisi `p` milik VM dengan pola `desc` (konstanta chunk): 0/1 = hasilnya, posisinya
/// dilepas; 2 = jumlah sub-polanya salah, belum ada yang berubah (VM yang melaporkannya).
pub extern "C" fn pola(p: i64, desc: *const VmValue) -> i32 {
    let (vm, basis) = konteks();
    let v = sediakan(vm, basis, p as usize);
    match crate::vm::cocok_enum(v, unsafe { &*desc }) {
        Ok(b) => { *v = VmValue::Nil; b as i32 }
        Err(_) => 2,
    }
}

/// `AmbilPayload`: posisi `p` diganti payload enumnya; 1 = tidak berpayload (VM yang melaporkannya).
pub extern "C" fn payload(p: i64) -> i32 {
    let (vm, basis) = konteks();
    let v = sediakan(vm, basis, p as usize);
    let Some((_, _, Some(isi))) = v.bagian_enum() else { return 1 };
    *v = isi.clone();
    0
}

/// Isi lokal `slot` bingkai terluar dibaca di tempat (sel lewat kuncinya); `None` = di luar stack.
fn lihat_lokal<T>(slot: i64, f: impl FnOnce(&VmValue) -> T) -> Option<T> {
    let (vm, basis) = konteks();
    Some(match vm.stack.get(basis + slot as usize)? {
        VmValue::Cell(c) => f(&c.lock().unwrap_or_else(|p| p.into_inner())),
        v => f(v),
    })
}

/// `LoadLocal` + `CekEnum` tanpa menyalin lokalnya: 0/1 = hasil; 2 = VM yang menjalankan keduanya.
pub extern "C" fn pola_lokal(slot: i64, desc: *const VmValue) -> i32 {
    lihat_lokal(slot, |v| crate::vm::cocok_enum(v, unsafe { &*desc }).map_or(2, |b| b as i32)).unwrap_or(2)
}

/// `LoadLocal` + `AmbilPayload`: posisi `ke` = payload lokal `slot`; 1 = VM yang menjalankan keduanya.
pub extern "C" fn payload_lokal(slot: i64, ke: i64) -> i32 {
    let Some(Some(isi)) = lihat_lokal(slot, |v| match v.bagian_enum() {
        Some((_, _, Some(isi))) => Some(isi.clone()),
        _ => None,
    }) else { return 1 };
    let (vm, basis) = konteks();
    *sediakan(vm, basis, ke as usize) = isi;
    0
}

/// `LoadLocal` yang langsung dibuka (`buka`) tanpa menyalin lokalnya ke stack VM.
pub extern "C" fn buka_lokal(slot: i64, jenis: i32, keluar: *mut i64) -> i32 {
    let n = lihat_lokal(slot, |v| match (v, jenis) {
        (VmValue::Int(n), 1) => i64::try_from(*n).ok(),
        (VmValue::Float(x), 5) => Some(x.to_bits() as i64),
        _ => None,
    }).flatten();
    match n {
        Some(n) => { unsafe { *keluar = n }; 0 }
        None => 1,
    }
}

/// `IterAda` atas iterator di posisi `slot` (tiga posisi milik VM): 0/1 = masih ada; 2 = VM yang melapor.
pub extern "C" fn iter_ada(slot: i64) -> i32 {
    let (vm, basis) = konteks();
    vm.iter_ada(basis + slot as usize, None).map_or(2, |b| b as i32)
}

/// `IterMaju`: indeks iterator di posisi `slot` (bulat milik VM) maju satu; 1 = bukan bulat (VM yang melapor).
pub extern "C" fn maju(slot: i64) -> i32 {
    let (vm, basis) = konteks();
    match vm.stack.get_mut(basis + slot as usize) {
        Some(VmValue::Int(n)) if *n < i128::MAX => { *n += 1; 0 }
        _ => 1,
    }
}

/// `SlideDown`: posisi `dari` (milik VM) pindah ke `ke`; yang tertinggal di `dari` jadi `nil`.
pub extern "C" fn pindah(dari: i64, ke: i64) {
    let (vm, basis) = konteks();
    let v = std::mem::replace(sediakan(vm, basis, dari as usize), VmValue::Nil);
    *sediakan(vm, basis, ke as usize) = v;
}

/// `LoadGlobal`: posisi `ke` = global `nama` (isi sel `var` modul); 1 = tidak ada (VM yang melapor).
pub extern "C" fn muat_global(nama: *const String, ke: i64) -> i32 {
    let (vm, basis) = konteks();
    let v = match vm.globals.get(unsafe { &*nama }) {
        Some(VmValue::Cell(sel)) => sel.lock().unwrap_or_else(|p| p.into_inner()).clone(),
        Some(v) => v.clone(),
        None => return 1,
    };
    *sediakan(vm, basis, ke as usize) = v;
    0
}

/// `LoadUpval`: posisi `ke` = isi sel tangkapan ke-`idx` closure bingkai terluar; 1 = tidak ada (VM yang melapor).
pub extern "C" fn muat_upval(idx: i64, ke: i64) -> i32 {
    let (vm, basis) = konteks();
    let Ok(sel) = vm.upval_at(idx as u32, None) else { return 1 };
    let v = sel.lock().unwrap_or_else(|p| p.into_inner()).clone();
    *sediakan(vm, basis, ke as usize) = v;
    0
}

/// `StoreUpval`: sel tangkapan ke-`idx` = nilai posisi `dari` berjenis `jenis` (kode `simpan`); 1 = tidak ada.
pub extern "C" fn simpan_upval(idx: i64, dari: i64, nilai: i64, jenis: i32) -> i32 {
    let (vm, basis) = konteks();
    let Ok(sel) = vm.upval_at(idx as u32, None) else { return 1 };
    let v = match jenis {
        1 => VmValue::Int(nilai as i128),
        2 => VmValue::Bool(nilai != 0),
        3 => VmValue::Nil,
        5 => VmValue::Float(f64::from_bits(nilai as u64)),
        _ => sediakan(vm, basis, dari as usize).clone(),
    };
    *sel.lock().unwrap_or_else(|p| p.into_inner()) = v;
    0
}

/// `StoreGlobal`: sel `var` modul `nama` = nilai posisi `dari` berjenis `jenis` (kode `simpan`);
/// 1 = bukan `var` yang sudah didefinisikan (VM yang melapor), belum ada yang berubah.
pub extern "C" fn simpan_global(nama: *const String, dari: i64, nilai: i64, jenis: i32) -> i32 {
    let (vm, basis) = konteks();
    let v = match jenis {
        1 => VmValue::Int(nilai as i128),
        2 => VmValue::Bool(nilai != 0),
        3 => VmValue::Nil,
        5 => VmValue::Float(f64::from_bits(nilai as u64)),
        _ => sediakan(vm, basis, dari as usize).clone(),
    };
    match vm.globals.get(unsafe { &*nama }) {
        Some(VmValue::Cell(sel)) => { *sel.lock().unwrap_or_else(|p| p.into_inner()) = v; 0 }
        _ => 1,
    }
}

/// `GetIndex`: posisi `p` (wadah milik VM) diganti elemennya; indeksnya bulat/bool/pecahan (`jenis`,
/// kode `simpan`) atau milik VM di `p + 1`. 1 = galat, belum ada yang berubah (VM yang melapor).
pub extern "C" fn indeks(p: i64, nilai: i64, jenis: i32) -> i32 {
    let (vm, basis) = konteks();
    let i = basis + p as usize;
    let idx = match jenis {
        1 => VmValue::Int(nilai as i128),
        2 => VmValue::Bool(nilai != 0),
        3 => VmValue::Nil,
        5 => VmValue::Float(f64::from_bits(nilai as u64)),
        _ => match vm.stack.get(i + 1) { Some(v) => v.clone(), None => return 1 },
    };
    let Some(wadah) = vm.stack.get(i) else { return 1 };
    match vm.get_index(wadah, &idx, None) {
        Ok(v) => { vm.stack[i] = v; 0 }
        Err(_) => 1,
    }
}

/// `GetField`/`GetFieldPrivat` (`privat` 1): posisi `p` (milik VM) diganti field `nama`-nya. 1 = galat
/// atau method `math::` yang ditulis tanpa `()` (VM yang menjalankannya), belum ada yang berubah.
pub extern "C" fn field(p: i64, nama: *const String, privat: i32) -> i32 {
    let (vm, basis) = konteks();
    let (i, nama) = (basis + p as usize, unsafe { &*nama });
    let Some(obj) = vm.stack.get(i) else { return 1 };
    if privat != 0 && vm.periksa_visibilitas(obj, nama, None).is_err() { return 1; }
    match vm.get_field(obj, nama, None) {
        Ok(VmValue::NativeFn(_)) if matches!(obj, VmValue::Float(_) | VmValue::Int(_)) => 1,
        Ok(v) => { vm.stack[i] = v; 0 }
        Err(_) => 1,
    }
}

/// `Dup` atas posisi `dari` milik VM: posisi `ke` = salinannya.
pub extern "C" fn salin(dari: i64, ke: i64) {
    let (vm, basis) = konteks();
    let v = sediakan(vm, basis, dari as usize).clone();
    *sediakan(vm, basis, ke as usize) = v;
}

/// `Swap` atas dua posisi milik VM.
pub extern "C" fn tukar(x: i64, y: i64) {
    let (vm, basis) = konteks();
    sediakan(vm, basis, x.max(y) as usize);
    vm.stack.swap(basis + x as usize, basis + y as usize);
}

/// Jaga tembolok method: penerima di posisi `p` berlabel `label`; lolos = posisinya dilepas (dipakai
/// `GetMethod`) dan galat method tertunda di atasnya dibuang, seperti `op_get_method` yang berhasil.
/// 1 = label lain, belum ada yang berubah.
pub extern "C" fn cek_metode(p: i64, label: *const String) -> i32 {
    let (vm, basis) = konteks();
    let v = sediakan(vm, basis, p as usize);
    if v.nama_tipe() != Some(unsafe { (*label).as_str() }) { return 1; }
    *v = VmValue::Nil;
    let slot = (basis + p as usize).saturating_sub(1);
    if !vm.galat_metode.is_empty() { vm.galat_metode.retain(|(i, _)| *i < slot); }
    0
}

/// Tepi ke titik temu yang dilebarkan: angka native di posisi `p` jadi nilai VM (kode jenis `simpan`).
pub extern "C" fn tulis_vm(p: i64, nilai: i64, jenis: i32) {
    let (vm, basis) = konteks();
    let v = match jenis {
        1 => VmValue::Int(nilai as i128),
        2 => VmValue::Bool(nilai != 0),
        5 => VmValue::Float(f64::from_bits(nilai as u64)),
        _ => VmValue::Nil,
    };
    *sediakan(vm, basis, p as usize) = v;
}

/// `Jenis::Lebar` di posisi `p` ke stack VM: bulat i128 dari dua belahan 64 bit.
pub extern "C" fn tulis_lebar(p: i64, lo: i64, hi: i64) {
    let (vm, basis) = konteks();
    *sediakan(vm, basis, p as usize) = VmValue::Int(((hi as i128) << 64) | (lo as u64 as i128));
}

/// Posisi `p` (milik VM) sebagai bulat i128: `keluar[0]` belahan bawah, `keluar[1]` atas; 1 = bukan bulat.
pub extern "C" fn buka_lebar(p: i64, keluar: *mut i64) -> i32 {
    let (vm, basis) = konteks();
    match vm.stack.get(basis + p as usize) {
        Some(VmValue::Int(n)) => {
            unsafe { *keluar = *n as i64; *keluar.add(1) = (*n >> 64) as i64; }
            0
        }
        _ => 1,
    }
}

/// Posisi `p` dilepas (`Pop` atas nilai milik VM).
pub extern "C" fn buang(p: i64) {
    let (vm, basis) = konteks();
    if let Some(v) = vm.stack.get_mut(basis + p as usize) { *v = VmValue::Nil; }
}

/// Truthiness posisi `p` (`VmValue::is_truthy`); `lepas` = posisinya dibuang sesudahnya.
pub extern "C" fn benar(p: i64, lepas: i32) -> i32 {
    let (vm, basis) = konteks();
    let Some(v) = vm.stack.get_mut(basis + p as usize) else { return 0 };
    let b = v.is_truthy();
    if lepas != 0 { *v = VmValue::Nil; }
    b as i32
}

/// Posisi `p` sebagai bulat 64 bit (`jenis` 1) atau pecahan (5) di `*keluar`; 1 = jenisnya lain.
pub extern "C" fn buka(p: i64, jenis: i32, keluar: *mut i64) -> i32 {
    let (vm, basis) = konteks();
    let v = match (vm.stack.get(basis + p as usize), jenis) {
        (Some(VmValue::Int(n)), 1) => i64::try_from(*n).ok(),
        (Some(VmValue::Float(x)), 5) => Some(x.to_bits() as i64),
        _ => None,
    };
    match v {
        Some(n) => { unsafe { *keluar = n }; 0 }
        None => 1,
    }
}

/// Pasang konteks selama `f` (kode native) berjalan; konteks sebelumnya dipulihkan.
pub(crate) fn dengan_konteks<T>(vm: *mut Vm, basis: usize, f: impl FnOnce() -> T) -> T {
    let lama = KONTEKS.with(|k| k.replace((vm, basis)));
    let h = f();
    KONTEKS.with(|k| k.set(lama));
    h
}

/// Slot lokal `rel` bingkai terluar sebagai larik (bukan sel tangkapan): `f` atas isinya.
fn atas_larik<T>(rel: i64, f: impl FnOnce(&mut VmValue) -> Option<T>) -> Option<T> {
    let (vm, basis) = KONTEKS.with(|k| k.get());
    if vm.is_null() { return None; }
    // Kode native berjalan di dalam `panggil::jalankan`, yang tidak menyentuh VM sampai kode itu kembali.
    let vm = unsafe { &mut *vm };
    let tempat = vm.stack.get_mut(basis.checked_add(usize::try_from(rel).ok()?)?)?;
    if !matches!(tempat, VmValue::Array(_)) { return None; }
    f(tempat)
}

/// Indeks dengan aturan `norm_idx` (negatif dari belakang); di luar batas = `None` (VM yang menolak).
fn norm_indeks(i: i64, n: usize) -> Option<usize> {
    let i = if i < 0 { n as i128 + i as i128 } else { i as i128 };
    (0..n as i128).contains(&i).then_some(i as usize)
}

/// `IndeksLokal` atas larik berelemen bulat 64 bit: 0 = `*keluar` terisi.
pub extern "C" fn baca(rel: i64, i: i64, keluar: *mut i64) -> i32 {
    let v = atas_larik(rel, |t| {
        let VmValue::Array(a) = t else { return None };
        let g = a.lock().unwrap_or_else(|p| p.into_inner());
        match g.get(norm_indeks(i, g.len())?)? {
            VmValue::Int(n) => i64::try_from(*n).ok(),
            _ => None,
        }
    });
    match v {
        Some(n) => { unsafe { *keluar = n }; 0 }
        None => 1,
    }
}

/// `TulisIndexLokal`: elemen ke-`i` = nilai berjenis `jenis` (1 bulat, 2 bool, 5 pecahan); 0 = tertulis.
pub extern "C" fn tulis(rel: i64, i: i64, nilai: i64, jenis: i32) -> i32 {
    let v = match jenis {
        1 => VmValue::Int(nilai as i128),
        2 => VmValue::Bool(nilai != 0),
        5 => VmValue::Float(f64::from_bits(nilai as u64)),
        _ => return 1,
    };
    let ok = atas_larik(rel, |t| {
        // Aturan `PinjamLokal`: isi dipisahkan dari pemegang lain sebelum ditulis (tidak terlihat bila gagal).
        t.pisahkan();
        let VmValue::Array(a) = t else { return None };
        let mut g = a.lock().unwrap_or_else(|p| p.into_inner());
        let k = norm_indeks(i, g.len())?;
        g[k] = v;
        Some(())
    });
    if ok.is_some() { 0 } else { 1 }
}
