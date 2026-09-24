use std::{
    cell::Cell,
    cmp::Ordering,
    ffi::{c_char, c_int, c_long, c_ulong},
    fmt,
};
#[cfg(not(all(target_endian = "little", target_pointer_width = "64")))]
compile_error!("The GMP limb ABI requires a little-endian 64-bit target");
#[repr(C)]
struct Raw {
    alloc: c_int,
    size: c_int,
    limbs: *mut u64,
}
extern "C" {
    fn __gmpz_init(p: *mut Raw);
    fn __gmpz_clear(p: *mut Raw);
    fn __gmpz_set(p: *mut Raw, q: *const Raw);
    fn __gmpz_set_si(p: *mut Raw, n: c_long);
    fn __gmpz_set_ui(p: *mut Raw, n: c_ulong);
    fn __gmpz_get_str(s: *mut c_char, base: c_int, p: *const Raw) -> *mut c_char;
    fn __gmpz_sizeinbase(p: *const Raw, base: c_int) -> usize;
    fn __gmpz_cmp(p: *const Raw, q: *const Raw) -> c_int;
    fn __gmpz_add(p: *mut Raw, a: *const Raw, b: *const Raw);
    fn __gmpz_sub(p: *mut Raw, a: *const Raw, b: *const Raw);
    fn __gmpz_mul(p: *mut Raw, a: *const Raw, b: *const Raw);
    fn __gmpz_mul_si(p: *mut Raw, a: *const Raw, b: c_long);
    fn __gmpz_mul_2exp(p: *mut Raw, a: *const Raw, b: c_ulong);
    fn __gmpz_add_ui(p: *mut Raw, a: *const Raw, b: c_ulong);
    fn __gmpz_sub_ui(p: *mut Raw, a: *const Raw, b: c_ulong);
    fn __gmpz_fdiv_q(p: *mut Raw, a: *const Raw, b: *const Raw);
    fn __gmpz_fdiv_r(p: *mut Raw, a: *const Raw, b: *const Raw);
    fn __gmpz_fdiv_q_2exp(p: *mut Raw, a: *const Raw, b: c_ulong);
    fn __gmpz_fdiv_r_2exp(p: *mut Raw, a: *const Raw, b: c_ulong);
    fn __gmpz_fdiv_ui(a: *const Raw, b: c_ulong) -> c_ulong;
    fn __gmpz_divexact(p: *mut Raw, a: *const Raw, b: *const Raw);
    fn __gmpz_divisible_p(a: *const Raw, b: *const Raw) -> c_int;
    fn __gmpz_divisible_2exp_p(a: *const Raw, b: c_ulong) -> c_int;
    fn __gmpz_gcd(p: *mut Raw, a: *const Raw, b: *const Raw);
    fn __gmpz_ui_pow_ui(p: *mut Raw, a: c_ulong, b: c_ulong);
    fn __gmpz_scan1(a: *const Raw, start: c_ulong) -> c_ulong;
    fn __gmpz_popcount(a: *const Raw) -> c_ulong;
    fn tm_mod3(limbs: *const u64, count: usize) -> u64;
    fn tm_set_dyadic(
        out: *mut Raw,
        input: *const Raw,
        slope: i64,
        constant: i64,
        shift: u64,
    ) -> bool;
}
pub struct Big {
    raw: Raw,
    mod3: Cell<Option<u64>>,
}
impl Big {
    pub fn new() -> Self {
        let mut n = Self {
            raw: Raw {
                alloc: 0,
                size: 0,
                limbs: std::ptr::null_mut(),
            },
            mod3: Cell::new(None),
        };
        unsafe { __gmpz_init(&mut n.raw) };
        n
    }
    pub fn i(value: i64) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_set_si(&mut n.raw, value) };
        n
    }
    pub fn u(value: u64) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_set_ui(&mut n.raw, value) };
        n
    }
    pub fn text(&self, base: i32) -> String {
        let capacity = unsafe { __gmpz_sizeinbase(&self.raw, base) } + 3;
        let mut out = vec![0u8; capacity];
        unsafe { __gmpz_get_str(out.as_mut_ptr().cast(), base, &self.raw) };
        out.truncate(out.iter().position(|&b| b == 0).unwrap());
        String::from_utf8(out).unwrap()
    }
    pub fn sign(&self) -> i32 {
        self.raw.size.signum()
    }
    pub fn bits(&self) -> usize {
        let words = self.limbs();
        words.last().map_or(0, |v| {
            64 * (words.len() - 1) + (64 - v.leading_zeros()) as usize
        })
    }
    pub fn limbs(&self) -> &[u64] {
        if self.raw.size == 0 {
            &[]
        } else {
            unsafe {
                std::slice::from_raw_parts(self.raw.limbs, self.raw.size.unsigned_abs() as usize)
            }
        }
    }
    pub fn as_u64(&self) -> Option<u64> {
        if self.sign() < 0 || self.bits() > 64 {
            None
        } else {
            Some(self.limbs().first().copied().unwrap_or(0))
        }
    }
    pub fn as_i64(&self) -> Option<i64> {
        if self.bits() > 63 {
            return None;
        }
        let v = self.limbs().first().copied().unwrap_or(0) as i64;
        Some(if self.sign() < 0 { -v } else { v })
    }
    pub fn cmp(&self, other: &Self) -> Ordering {
        unsafe { __gmpz_cmp(&self.raw, &other.raw) }.cmp(&0)
    }
    pub fn neg(&self) -> Self {
        let mut n = self.clone();
        n.raw.size = -n.raw.size;
        n.mod3.set(self.mod3.get().map(|r| (3 - r) % 3));
        n
    }
    pub fn add(&self, other: &Self) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_add(&mut n.raw, &self.raw, &other.raw) };
        n
    }
    pub fn sub(&self, other: &Self) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_sub(&mut n.raw, &self.raw, &other.raw) };
        n
    }
    pub fn mul(&self, other: &Self) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_mul(&mut n.raw, &self.raw, &other.raw) };
        n
    }
    pub fn floor(&self, other: &Self) -> Self {
        assert!(other.sign() > 0);
        let mut n = Self::new();
        unsafe { __gmpz_fdiv_q(&mut n.raw, &self.raw, &other.raw) };
        n
    }
    pub fn modulo(&self, other: &Self) -> Self {
        assert!(other.sign() > 0);
        let mut n = Self::new();
        unsafe { __gmpz_fdiv_r(&mut n.raw, &self.raw, &other.raw) };
        n
    }
    pub fn mod_u(&self, n: u64) -> u64 {
        assert!(n > 0);
        if n == 3 {
            if let Some(r) = self.mod3.get() {
                return r;
            }
            let limbs = self.limbs();
            let r = unsafe { tm_mod3(limbs.as_ptr(), limbs.len()) };
            let r = if self.sign() < 0 && r != 0 { 3 - r } else { r };
            self.mod3.set(Some(r));
            return r;
        }
        unsafe { __gmpz_fdiv_ui(&self.raw, n) }
    }
    pub fn exact(&self, other: &Self) -> Self {
        assert!(
            other.sign() > 0 && unsafe { __gmpz_divisible_p(&self.raw, &other.raw) } != 0,
            "nonexact quotient"
        );
        let mut n = Self::new();
        unsafe { __gmpz_divexact(&mut n.raw, &self.raw, &other.raw) };
        n
    }
    pub fn shr(&self, bits: u64) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_fdiv_q_2exp(&mut n.raw, &self.raw, bits) };
        n
    }
    pub fn shl(&self, bits: u64) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_mul_2exp(&mut n.raw, &self.raw, bits) };
        n
    }
    pub fn low(&self, bits: u64) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_fdiv_r_2exp(&mut n.raw, &self.raw, bits) };
        n
    }
    pub fn gcd(&self, other: &Self) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_gcd(&mut n.raw, &self.raw, &other.raw) };
        n
    }
    pub fn pow(base: u64, exp: u64) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_ui_pow_ui(&mut n.raw, base, exp) };
        n
    }
    pub fn valuation(&self) -> u64 {
        assert!(self.sign() > 0);
        unsafe { __gmpz_scan1(&self.raw, 0) }
    }
    pub fn population(&self) -> u64 {
        assert!(self.sign() >= 0);
        unsafe { __gmpz_popcount(&self.raw) }
    }
    pub fn set_dyadic(&mut self, input: &Self, slope: i64, constant: i64, shift: u64) {
        self.mod3.set(input.mod3.get().map(|r| {
            ((r * slope.rem_euclid(3) as u64 + constant.rem_euclid(3) as u64)
                * if shift % 2 == 0 { 1 } else { 2 })
                % 3
        }));
        unsafe {
            if tm_set_dyadic(&mut self.raw, &input.raw, slope, constant, shift) {
                return;
            }
            __gmpz_mul_si(&mut self.raw, &input.raw, slope);
            if constant >= 0 {
                __gmpz_add_ui(&mut self.raw, &self.raw, constant as u64)
            } else {
                __gmpz_sub_ui(&mut self.raw, &self.raw, constant.unsigned_abs())
            }
            assert!(
                __gmpz_divisible_2exp_p(&self.raw, shift) != 0,
                "nonexact dyadic quotient"
            );
            __gmpz_fdiv_q_2exp(&mut self.raw, &self.raw, shift);
        }
    }
    pub fn set_expression(&mut self, input: &Self, a: &Self, c: &Self, d: &Self) {
        self.mod3.set(None);
        if let (Some(a), Some(c)) = (a.as_i64(), c.as_i64()) {
            if d.sign() > 0 && d.population() == 1 {
                self.set_dyadic(input, a, c, d.valuation());
                return;
            }
        }
        unsafe {
            __gmpz_mul(&mut self.raw, &input.raw, &a.raw);
            __gmpz_add(&mut self.raw, &self.raw, &c.raw);
            assert!(
                d.sign() > 0 && __gmpz_divisible_p(&self.raw, &d.raw) != 0,
                "nonexact affine quotient"
            );
            __gmpz_divexact(&mut self.raw, &self.raw, &d.raw);
        }
    }
}
impl Clone for Big {
    fn clone(&self) -> Self {
        let mut n = Self::new();
        unsafe { __gmpz_set(&mut n.raw, &self.raw) };
        n.mod3.set(self.mod3.get());
        n
    }
}
impl Drop for Big {
    fn drop(&mut self) {
        unsafe { __gmpz_clear(&mut self.raw) }
    }
}
impl PartialEq for Big {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for Big {}
impl fmt::Debug for Big {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.text(10))
    }
}
