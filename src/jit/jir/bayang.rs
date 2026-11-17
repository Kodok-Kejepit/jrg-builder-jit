//! Bayangan varian (JIR-3b langkah 1): posisi stack berisi varian enum yang penanda dan payload angkanya diketahui
//! sebagai isi native. Stack VM tetap memegang nilai yang benar (deopt membacanya); bayangan menggantikan `pola_pilih`
//! dan bukaan payload, dibawa lintas titik temu sebagai parameter blok tambahan.

use std::collections::HashMap;

use super::{Akhir, Arg, Banding, Biner, Blok, Inst, Jenis, Nilai, Pb, Pembangun, Tipe};
use crate::vm::value::{Label, NamaVarian, VmValue};

#[derive(Clone, Debug, PartialEq)]
pub(super) struct Bayang {
    /// Indeks varian di `Pembangun::varian`.
    pub tag: Nilai,
    /// Bit tag yang mungkin.
    pub mungkin: u64,
    /// Isi payload: jenisnya (`Bulat`/`Pecahan`), nilainya, dan bit tag yang payload-nya memang isi ini.
    pub muatan: Vec<(Jenis, Nilai, u64)>,
}

/// Bayangan per posisi, urut posisi.
pub(super) type Potret = Vec<(usize, Bayang)>;

/// Posisi stack yang ditulis `i`; `None` = tidak diketahui (dianggap semua).
pub(super) fn ditulis(i: &Inst) -> Option<Vec<usize>> {
    Some(match i {
        Inst::KonstI { .. } | Inst::KonstF { .. } | Inst::KonstL { .. } | Inst::Biner { .. } | Inst::Unar { .. }
        | Inst::BinerL { .. } | Inst::Pilih { .. } | Inst::JagaJika { .. } | Inst::Undi { .. } | Inst::Sempit { .. }
        | Inst::Rantai { .. } | Inst::CekMetode { .. } | Inst::IterAda { .. } => vec![],
        Inst::Muat { lokal, ke, pindah } => if *pindah { vec![*ke, *lokal] } else { vec![*ke] },
        Inst::Simpan { ke, dari, buang, .. } => if *buang { vec![*ke, *dari] } else { vec![*ke] },
        Inst::Salin { ke, .. } => vec![*ke],
        Inst::Pindah { dari, ke } => vec![*ke, *dari],
        Inst::Tukar { x, y } => vec![*x, *y],
        Inst::Buang { pos } | Inst::Taruh { pos, .. } | Inst::TulisVm { pos, .. } | Inst::TulisLebar { pos, .. }
        | Inst::TeksBulat { pos, .. } | Inst::Sebar { pos, .. } | Inst::Buka { pos, .. } | Inst::BukaLebar { pos, .. } => vec![*pos],
        Inst::Maju { slot, .. } => vec![*slot],
        Inst::Benar { pos, lepas, .. } => if *lepas { vec![*pos] } else { vec![] },
        Inst::Panjang { pos, lokal, .. } => if *lokal { vec![] } else { vec![*pos] },
        Inst::Bangun { t, n, .. } => (t - n..*t).collect(),
        Inst::Rumus { lokal, .. } => vec![*lokal],
        Inst::Pembantu { pb, args, .. } => {
            let pos = |k: usize| match args.get(k) { Some(Arg::I64(p)) => Some(*p as usize), _ => None };
            match pb {
                Pb::PolaLokal | Pb::PayloadJenisSama | Pb::PayloadPanjang | Pb::KarakterLokal => vec![],
                Pb::PayloadLokal | Pb::PayloadAngkaLokal => pos(1).into_iter().collect(),
                Pb::FieldLokal => pos(3).into_iter().collect(),
                pb => super::posisi_pb(*pb).iter().filter_map(|k| pos(*k)).collect(),
            }
        }
        _ => return None,
    })
}

impl Pembangun<'_> {
    pub(super) fn tag_varian(&mut self, nama: &'static NamaVarian, payload: Option<usize>) -> Option<u32> {
        let i = match self.varian.iter().position(|(n, p)| std::ptr::eq(*n, nama) && *p == payload) {
            Some(i) => i,
            None => { self.varian.push((nama, payload)); self.varian.len() - 1 }
        };
        (i < 64).then_some(i as u32)
    }

    /// Posisi `pos` kini varian `nama` dengan payload `muatan` (atau tanpa isi native: `payload` jumlahnya saja).
    pub(super) fn lahir_varian(&mut self, b: Blok, pos: usize, nama: &'static NamaVarian, payload: Option<usize>, muatan: Vec<(Jenis, Nilai)>) {
        if !self.bayang_aktif { return; }
        let Some(i) = self.tag_varian(nama, payload) else { return };
        let tag = self.konst_i(b, i as i64);
        let bit = 1u64 << i;
        self.bayang.insert(pos, Bayang { tag, mungkin: bit, muatan: muatan.into_iter().map(|(j, v)| (j, v, bit)).collect() });
        self.lahir.push(pos);
    }

    /// Konstanta ke-`k` yang berupa varian tanpa payload.
    pub(super) fn lahir_konst(&mut self, b: Blok, pos: usize, k: usize) {
        if let Some(VmValue::Map(m)) = self.f.chunk.constants.get(k) {
            if let Label::Enum { nama, payload: None } = &m.label { self.lahir_varian(b, pos, nama, None, Vec::new()); }
        }
    }

    pub(super) fn salin_bayang(&mut self, dari: usize, ke: usize) {
        match self.bayang.get(&dari).cloned() {
            Some(x) => { self.bayang.insert(ke, x); self.lahir.push(ke); }
            None => { self.bayang.remove(&ke); }
        }
    }

    /// Instruksi `i` didorong ke blok yang sedang dibangun: bayangan posisi yang ditulisnya ikut berpindah atau hilang.
    pub(super) fn bayang_inst(&mut self, i: &Inst) {
        match i {
            Inst::Muat { lokal, ke, pindah } => { self.salin_bayang(*lokal, *ke); if *pindah { self.bayang.remove(lokal); } }
            Inst::Simpan { ke, dari, buang, .. } => { self.salin_bayang(*dari, *ke); if *buang { self.bayang.remove(dari); } }
            Inst::Salin { dari, ke } => self.salin_bayang(*dari, *ke),
            Inst::Pindah { dari, ke } => { self.salin_bayang(*dari, *ke); self.bayang.remove(dari); }
            Inst::Tukar { x, y } => {
                let (a, b) = (self.bayang.remove(x), self.bayang.remove(y));
                if let Some(a) = a { self.bayang.insert(*y, a); self.lahir.push(*y); }
                if let Some(b) = b { self.bayang.insert(*x, b); self.lahir.push(*x); }
            }
            // Panggilan tidak menyentuh lokal di bawah posisi fungsinya (nilai tidak beralias; tanpa closure).
            Inst::Langsung { t, a, .. } => { let d = t - a - 1; self.bayang.retain(|p, _| *p < d); }
            Inst::Bawaan { t, argc, .. } => { let d = t.saturating_sub((*argc as usize & 0xffff) + 1); self.bayang.retain(|p, _| *p < d); }
            Inst::BinerVm { t, .. } => { let d = t.saturating_sub(2); self.bayang.retain(|p, _| *p < d); }
            Inst::MuatUpval { ke, .. } => { self.bayang.remove(ke); }
            i => match ditulis(i) {
                Some(ps) => for p in ps { self.bayang.remove(&p); },
                None => self.bayang.clear(),
            },
        }
    }

    /// Sesudah satu instruksi bytecode yang mulai dengan tinggi stack `t0`: posisi yang tersentuh puncak tanpa
    /// dilahirkan, di atas stack, atau berisi native tidak berbayangan.
    pub(super) fn rapikan_bayang(&mut self, t0: usize, isi: &[Option<super::Nilai>]) {
        let h = t0.min(isi.len());
        let lahir = std::mem::take(&mut self.lahir);
        self.bayang.retain(|p, _| (*p < h || lahir.contains(p)) && isi.get(*p).is_some_and(|v| v.is_none()));
    }

    /// Tepi dari blok `asal` ke pemimpin `ke` (blok `sasaran`) yang stack-nya `panjang`: argumen bayangan tambahan
    /// kalau bloknya sudah dibangun, selain itu dicatat untuk dipasang saat bloknya mulai.
    pub(super) fn tepi_bayang(&mut self, asal: Blok, sasaran: Blok, ke: usize, panjang: usize) -> Result<Vec<Nilai>, String> {
        let mut potret: Potret = self.bayang.iter().filter(|(p, _)| **p < panjang).map(|(p, b)| (*p, b.clone())).collect();
        potret.sort_by_key(|x| x.0);
        let Some(params) = self.masuk_bayang.get(&ke).cloned() else {
            self.sisi.entry(ke).or_default().push((asal, sasaran, potret));
            return Ok(Vec::new());
        };
        match self.args_bayang(asal, &params, &potret) {
            Some(args) => Ok(args),
            None => {
                self.ulang = Some(ke);
                Err(format!("bayangan varian di ip {ke} tidak cocok dengan tepi yang datang belakangan"))
            }
        }
    }

    /// Argumen parameter bayangan `params` dari potret tepi yang berangkat dari `asal`; `None` = tidak cocok.
    fn args_bayang(&mut self, asal: Blok, params: &Potret, potret: &Potret) -> Option<Vec<Nilai>> {
        let mut args = Vec::new();
        for (pos, pb) in params {
            let e = potret.iter().find(|(p, _)| p == pos).map(|x| x.1.clone()).filter(|e| {
                e.mungkin & !pb.mungkin == 0 && pb.muatan.iter().enumerate().all(|(k, (j, _, sah))| {
                    let perlu = e.mungkin & sah;
                    perlu == 0 || e.muatan.get(k).is_some_and(|(je, _, se)| je == j && perlu & !se == 0)
                })
            })?;
            args.push(e.tag);
            for (k, (j, _, _)) in pb.muatan.iter().enumerate() {
                let v = match e.muatan.get(k) { Some((je, v, _)) if je == j => *v, _ => self.isi_nol(asal, *j) };
                args.push(v);
            }
        }
        Some(args)
    }

    fn isi_nol(&mut self, b: Blok, j: Jenis) -> Nilai {
        if j == Jenis::Pecahan {
            let h = self.j.nilai_baru(Tipe::F);
            self.dorong(b, Inst::KonstF { hasil: h, nilai: 0.0 });
            h
        } else { self.konst_i(b, 0) }
    }

    /// Pemimpin `ip` (blok `b`) mulai dibangun: bayangan yang dibawa SEMUA tepi yang sudah tercatat jadi parameter
    /// tambahannya, dan tepi itu diberi argumennya. Tepi yang datang belakangan (loop) diperiksa `tepi_bayang`.
    pub(super) fn mulai_bayang(&mut self, ip: usize, b: Blok) {
        self.bayang.clear();
        self.lahir.clear();
        let mut tepi = self.sisi.remove(&ip).unwrap_or_default();
        let mut lihat = Vec::new();
        tepi.retain(|(a, s, _)| if lihat.contains(&(*a, *s)) { false } else { lihat.push((*a, *s)); true });
        if !self.bayang_aktif || self.larang.contains(&ip) || tepi.is_empty() {
            self.masuk_bayang.insert(ip, Vec::new());
            return;
        }
        let mut params: Potret = Vec::new();
        for (pos, _) in &tepi[0].2 {
            let semua: Vec<&Bayang> = tepi.iter().filter_map(|(_, _, p)| p.iter().find(|(q, _)| q == pos).map(|x| &x.1)).collect();
            if semua.len() != tepi.len() { continue; }
            let mungkin = semua.iter().fold(0, |m, e| m | e.mungkin);
            let lebar = semua.iter().map(|e| e.muatan.len()).max().unwrap_or(0);
            let mut muatan = Vec::new();
            for k in 0..lebar {
                let j = semua.iter().find_map(|e| e.muatan.get(k).map(|x| x.0)).expect("lebar dari salah satunya");
                if semua.iter().any(|e| e.muatan.get(k).is_some_and(|x| x.0 != j)) { break; }
                let ada = semua.iter().fold(0, |m, e| m | e.muatan.get(k).map_or(0, |x| x.2));
                let hilang = semua.iter().fold(0, |m, e| m | (e.mungkin & !e.muatan.get(k).map_or(0, |x| x.2)));
                let v = self.j.nilai_baru(if j == Jenis::Pecahan { Tipe::F } else { Tipe::I });
                muatan.push((j, v, ada & !hilang));
            }
            params.push((*pos, Bayang { tag: self.j.nilai_baru(Tipe::I), mungkin, muatan }));
        }
        for (_, x) in &params {
            let blok = &mut self.j.blok[b.0 as usize].params;
            blok.push(x.tag);
            blok.extend(x.muatan.iter().map(|m| m.1));
        }
        self.masuk_bayang.insert(ip, params.clone());
        for (asal, sasaran, potret) in tepi {
            let args = self.args_bayang(asal, &params, &potret).expect("tepi yang membentuk parameternya cocok");
            self.tempel_args(asal, sasaran, args);
        }
        self.bayang = params.into_iter().collect();
    }

    /// Argumen bayangan tepi `asal → sasaran` yang dicatat sebelum bloknya mulai, ditempel ke akhir `asal`.
    pub(super) fn tempel_args(&mut self, asal: Blok, sasaran: Blok, args: Vec<Nilai>) {
        let tambah = |ke: &Blok, xs: &mut Vec<Nilai>| if *ke == sasaran { xs.extend(args.iter().copied()) };
        match self.j.blok[asal.0 as usize].akhir.as_mut() {
            Some(Akhir::Lompat { ke, args }) => tambah(ke, args),
            Some(Akhir::Cabang { ya, ya_args, tidak, tidak_args, .. }) => { tambah(ya, ya_args); tambah(tidak, tidak_args); }
            Some(Akhir::CabangVm { tujuan, .. }) => for (ke, xs, _) in tujuan.iter_mut() { tambah(ke, xs) },
            _ => {}
        }
    }

    /// Bit tag `mungkin` yang memenuhi `pilih`, sebagai 0/1 dari `tag` (instruksinya ke `keluar`).
    pub(super) fn lipat_tag(&mut self, keluar: &mut Vec<Inst>, x: &Bayang, pilih: impl Fn(u32) -> bool) -> Nilai {
        let set: Vec<u32> = (0..64).filter(|t| x.mungkin >> t & 1 == 1 && pilih(*t)).collect();
        let semua = x.mungkin.count_ones() as usize;
        let konst = |s: &mut Self, keluar: &mut Vec<Inst>, n: i64| { let h = s.j.nilai_baru(Tipe::I); keluar.push(Inst::KonstI { hasil: h, nilai: n }); h };
        if set.is_empty() { return konst(self, keluar, 0); }
        if set.len() == semua { return konst(self, keluar, 1); }
        let mut acc: Option<Nilai> = None;
        for t in set {
            let k = konst(self, keluar, t as i64);
            let sama = self.j.nilai_baru(Tipe::I);
            keluar.push(Inst::Biner { hasil: sama, op: Biner::ICmp(Banding::Eq), a: x.tag, b: k, jaga: None });
            acc = Some(match acc {
                None => sama,
                Some(a) => { let h = self.j.nilai_baru(Tipe::I); keluar.push(Inst::Biner { hasil: h, op: Biner::IAtau, a, b: sama, jaga: None }); h }
            });
        }
        acc.expect("set tidak kosong")
    }

    /// Lengan `urutan` rantai `match` di alamat `situs` atas posisi berbayangan `x`: cocok tidaknya, kalau tiap
    /// varian yang mungkin terjawab tanpa galat saat kompilasi.
    pub(super) fn lipat_rantai(&mut self, keluar: &mut Vec<Inst>, x: &Bayang, situs: i64, urutan: usize) -> Option<Nilai> {
        let rantai = unsafe { &*(situs as *const crate::jit::lambat::RantaiPola) };
        let mut lengan = HashMap::new();
        for t in (0..64u32).filter(|t| x.mungkin >> t & 1 == 1) {
            let (nama, payload) = *self.varian.get(t as usize)?;
            lengan.insert(t, rantai.pilih_statis(nama, payload)?);
        }
        Some(self.lipat_tag(keluar, x, |t| lengan[&t] == urutan))
    }

    /// `payload_angka_lokal` atas posisi berbayangan `x` dengan spekulasi `j`: (status 0/1 seperti pembantunya —
    /// 1 = bukan varian yang payload-nya isi ini, deopt — dan isinya).
    pub(super) fn lipat_payload(&mut self, keluar: &mut Vec<Inst>, x: &Bayang, j: Jenis) -> Option<(Nilai, Nilai)> {
        let (jm, v, sah) = *x.muatan.first()?;
        if jm != j { return None; }
        let satu: u64 = (0..self.varian.len().min(64)).filter(|t| self.varian[*t].1 == Some(1)).fold(0, |m, t| m | 1 << t);
        let baik = sah & satu & x.mungkin;
        if baik == 0 { return None; }
        let st = self.lipat_tag(keluar, x, |t| baik >> t & 1 == 0);
        Some((st, v))
    }

    /// Kumpulan instruksi ke blok `b` lewat `dorong` (supaya jejak bayangan dan CSE ikut).
    pub(super) fn dorong_semua(&mut self, b: Blok, xs: Vec<Inst>) { for i in xs { self.dorong(b, i); } }
}
