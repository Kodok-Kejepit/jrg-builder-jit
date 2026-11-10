//! JRGJIT, mesin eksekusi keempat (rancangan: `dokumentasi/jit/`). J1: VM berprofil; J2: kode mesin lewat
//! Cranelift (`j2-rencana.md`); J3: deopt di instruksi yang sama (`j3-rencana.md`); J4: titik keluar, nilai
//! milik VM di bingkai, OSR di kepala loop (`j4-rencana.md`).

pub mod profil;
pub mod laporan;
#[cfg(all(feature = "jit", not(target_arch = "wasm32")))]
pub mod layak;
#[cfg(all(feature = "jit", not(target_arch = "wasm32")))]
mod turun;
#[cfg(all(feature = "jit", not(target_arch = "wasm32")))]
pub(crate) mod modul;
#[cfg(all(feature = "jit", not(target_arch = "wasm32")))]
pub(crate) mod panggil;
#[cfg(all(feature = "jit", not(target_arch = "wasm32")))]
pub(crate) mod deopt;
#[cfg(all(feature = "jit", not(target_arch = "wasm32")))]
pub(crate) mod lambat;

use std::sync::atomic::{AtomicBool, Ordering};

static AKTIF: AtomicBool = AtomicBool::new(false);

/// Dinyalakan sekali oleh `jrgc --jit` sebelum program dikompilasi.
pub fn aktifkan() { AKTIF.store(true, Ordering::Relaxed); }

#[inline]
pub fn aktif() -> bool { AKTIF.load(Ordering::Relaxed) }

/// Pintu masuk kode native sebuah fungsi: `(args, kedalaman, keluar) -> status`.
#[derive(Clone, Copy)]
pub struct KodeJit {
    pub masuk: unsafe extern "C" fn(*const i64, i32, *mut i64) -> i32,
}

impl std::fmt::Debug for KodeJit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { f.write_str("<kode jit>") }
}

/// Panggilan ke-berapa sebuah fungsi dikompilasi (`JRG_JIT_AMBANG`, bawaan 2; 0 = mode stres).
pub fn ambang() -> u32 {
    static A: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *A.get_or_init(|| std::env::var("JRG_JIT_AMBANG").ok().and_then(|s| s.parse().ok()).unwrap_or(2))
}

/// Satu titik masuk kode native milik sebuah chunk; `kode: None` = sudah dicoba dan tidak layak.
pub struct Masuk {
    pub ip: u32,
    pub kembali: u8,
    /// Jenis tiap posisi stack bingkai di titik masuk (`layak::Jenis` sebagai kode).
    pub jenis: Box<[u8]>,
    pub kode: Option<KodeJit>,
}

/// Titik masuk native per chunk (dibagi goroutine, jadi di balik kunci).
#[derive(Default)]
pub struct PintuJit {
    pub masuk: std::sync::Mutex<Vec<Masuk>>,
    /// Masuk lewat panggilan pernah gagal dikompilasi: panggilan berikutnya langsung VM, tanpa kunci.
    pub panggilan_mati: std::sync::atomic::AtomicBool,
    /// Naik tiap kali kodenya dibuang (spekulasi gagal); bagian kunci tembolok `modul`.
    pub versi: std::sync::atomic::AtomicU32,
    /// Instruksi yang spekulasinya (nilai VM sebagai angka, larik berelemen angka) pernah gagal.
    pub spek_gagal: std::sync::Mutex<Vec<u32>>,
    /// Umpan `GetMethod`: situs, label tipe penerima pertama yang teramati, dan method pemakai-nya.
    pub metode: std::sync::Mutex<Vec<(u32, String, std::sync::Arc<crate::vm::value::VmFunction>)>>,
}

/// Spekulasi yang gagal lebih dari ini membuat chunk-nya berhenti dikompilasi ulang.
const MAKS_SPEK_GAGAL: usize = 16;

impl PintuJit {
    pub fn catat_metode(&self, ip: usize, label: String, f: std::sync::Arc<crate::vm::value::VmFunction>) {
        let mut g = self.metode.lock().unwrap_or_else(|p| p.into_inner());
        if !g.iter().any(|(i, ..)| *i == ip as u32) { g.push((ip as u32, label, f)); }
    }

    pub fn metode_di(&self, ip: usize) -> Option<(String, std::sync::Arc<crate::vm::value::VmFunction>)> {
        let g = self.metode.lock().unwrap_or_else(|p| p.into_inner());
        g.iter().find(|(i, ..)| *i == ip as u32).map(|(_, l, f)| (l.clone(), std::sync::Arc::clone(f)))
    }

    pub fn spek_gagal_di(&self, ip: usize) -> bool {
        self.spek_gagal.lock().unwrap_or_else(|p| p.into_inner()).contains(&(ip as u32))
    }

    /// Spekulasi di `ip` gagal: kodenya dibuang, kompilasi berikutnya tidak berspekulasi di sana.
    pub fn tandai_spek_gagal(&self, ip: usize) {
        let mut g = self.spek_gagal.lock().unwrap_or_else(|p| p.into_inner());
        if g.contains(&(ip as u32)) { return; }
        g.push(ip as u32);
        if g.len() > MAKS_SPEK_GAGAL { self.panggilan_mati.store(true, Ordering::Relaxed); }
        drop(g);
        self.versi.fetch_add(1, Ordering::Relaxed);
        self.masuk.lock().unwrap_or_else(|p| p.into_inner()).clear();
    }
}

// Salinan chunk (goroutine, closure) mulai tanpa kode; kodenya dikompilasi ulang bila perlu.
impl Clone for PintuJit {
    fn clone(&self) -> Self { PintuJit::default() }
}

impl std::fmt::Debug for PintuJit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { f.write_str("<pintu jit>") }
}

/// Berapa putaran sekali VM mencoba OSR di lompatan mundur (mode stres lebih sering).
pub fn osr_tiap() -> u32 { if ambang() == 0 { 4 } else { 1024 } }
