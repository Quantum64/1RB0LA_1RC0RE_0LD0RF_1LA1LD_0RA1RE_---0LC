use crate::{
    big::Big,
    prefix::{Cost, Prefix},
    scalar, transducer,
};
use std::ffi::{c_char, c_void, CStr, CString};
const BLOCK: usize = 4096;
const FOLD: usize = 32;
const MINIMUM_BITS: usize = 8192;
pub const MAX_GPU_INPUT_BITS: usize = (1usize << 32) - (1usize << 20);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mode {
    N202,
    N0002,
    N122,
    H,
}
impl Mode {
    pub fn period(self) -> u64 {
        match self {
            Self::N202 => 4,
            Self::H => 2,
            _ => 3,
        }
    }
    pub fn growth(self) -> i64 {
        match self {
            Self::N202 => 14,
            Self::H => 10,
            _ => 12,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Summary {
    pub head: u8,
    pub word: Vec<u8>,
    pub value: u64,
    pub loss: u64,
    pub base: u64,
    pub returns: u64,
    pub operations: u64,
}
impl Summary {
    pub fn mode(&self) -> Mode {
        if self.word.is_empty() {
            match (self.head, self.value) {
                (2, 2) => Mode::N202,
                (0, 4) => Mode::N0002,
                (1, 3) => Mode::N122,
                _ => panic!("nonterminal register summary"),
            }
        } else {
            assert!(self.head == 1 && self.value == 1 && self.word.iter().all(|&d| d == 3));
            Mode::H
        }
    }
}
extern "C" {
    fn tm_metal_create(
        shader: *const c_char,
        table: *const u8,
        table_size: usize,
        error: *mut c_char,
        size: usize,
    ) -> *mut c_void;
    fn tm_metal_destroy(context: *mut c_void);
    fn tm_metal_query(
        context: *mut c_void,
        words: *const u64,
        bits: u32,
        entry: bool,
        head: u32,
        len: u32,
        word: u64,
        output: *mut *const u32,
        size: *mut usize,
        prepared: *mut *const u64,
        prepared_bits: *mut u32,
        links: *mut *const u32,
    ) -> bool;
}
pub struct Normalizer {
    metal: *mut c_void,
}
impl Drop for Normalizer {
    fn drop(&mut self) {
        unsafe { tm_metal_destroy(self.metal) }
    }
}
impl Normalizer {
    pub fn new() -> Result<Self, String> {
        let source = CString::new(include_str!("register.metal")).unwrap();
        let table = transducer::derive();
        let mut error = [0i8; 2048];
        let metal = unsafe {
            tm_metal_create(
                source.as_ptr(),
                table.as_ptr(),
                table.len(),
                error.as_mut_ptr(),
                error.len(),
            )
        };
        if metal.is_null() {
            return Err(unsafe { CStr::from_ptr(error.as_ptr()) }
                .to_string_lossy()
                .into_owned());
        }
        Ok(Self { metal })
    }
    pub fn normalize(&mut self, value: &Big, head: u8, word: &[u8], width: u64) -> Summary {
        assert!(value.sign() > 0 && head <= 4 && word.iter().all(|d| matches!(d, 1 | 3)));
        if value.bits() >= MINIMUM_BITS {
            if let Some(result) = self.gpu(value, head, word, width, false) {
                return result;
            }
        }
        scalar::normalize(value.limbs(), head, word, width)
    }
    pub fn normalize_entry(&mut self, root: &Big, scratch: &mut Big, width: u64) -> Summary {
        let odd = root.limbs()[0] & 1 != 0;
        let head = if odd { 1 } else { 2 };
        let word: &[u8] = if odd { &[3] } else { &[] };
        if root.bits() >= MINIMUM_BITS {
            if let Some(result) = self.gpu(root, head, word, width, true) {
                return result;
            }
        }
        scratch.set_dyadic(root, 1, if odd { 10 } else { 12 }, if odd { 0 } else { 1 });
        scalar::normalize(scratch.limbs(), head, word, width)
    }
    pub(crate) fn gpu(
        &mut self,
        input: &Big,
        head: u8,
        odd: &[u8],
        width: u64,
        entry: bool,
    ) -> Option<Summary> {
        let source_bits = input.bits();
        let words = input.limbs();
        if odd.len() > 63 || source_bits == 0 || source_bits > MAX_GPU_INPUT_BITS {
            return None;
        }
        let mut state = Prefix::empty();
        state.head = head;
        state.len = odd.len() as u8;
        for (i, &d) in odd.iter().enumerate() {
            state.word |= ((d == 3) as u128) << i
        }
        if !state.valid() {
            return None;
        }
        let mut output = std::ptr::null();
        let mut size = 0;
        let mut prepared = std::ptr::null();
        let mut prepared_bits = 0;
        let mut links = std::ptr::null();
        let ok = unsafe {
            tm_metal_query(
                self.metal,
                words.as_ptr(),
                source_bits as u32,
                entry,
                head as u32,
                odd.len() as u32,
                state.word as u64,
                &mut output,
                &mut size,
                &mut prepared,
                &mut prepared_bits,
                &mut links,
            )
        };
        if !ok {
            return None;
        }
        let bits = prepared_bits as usize;
        if bits == 0
            || bits > MAX_GPU_INPUT_BITS
            || prepared.is_null()
            || (prepared as usize) % 8 != 0
        {
            return None;
        }
        let words = unsafe { std::slice::from_raw_parts(prepared, bits.div_ceil(64)) };
        let blocks = (bits - 1).div_ceil(BLOCK);
        let expected = 32 * blocks.div_ceil(FOLD);
        if size != expected || size > 134217728 {
            return None;
        }
        let rows = if size == 0 {
            &[][..]
        } else {
            if output.is_null() || (output as usize) % 4 != 0 {
                return None;
            }
            unsafe { std::slice::from_raw_parts(output, size) }
        };
        let links = if blocks == 0 {
            &[][..]
        } else {
            if links.is_null() || (links as usize) % 4 != 0 {
                return None;
            }
            unsafe { std::slice::from_raw_parts(links, 16 * blocks) }
        };
        let mut cost = Cost::default();
        for (index, r) in rows.chunks_exact(32).enumerate() {
            let start = index * FOLD * BLOCK;
            let end = (start + FOLD * BLOCK).min(bits - 1);
            let count = (blocks - index * FOLD).min(FOLD);
            if r[13] > 1 || r[14] > 1 || r[13] != r[14] {
                return None;
            }
            let accepted = if r[13] == 1 {
                let endpoint = Self::row_prefix(r)?;
                let seed = Self::row_prefix(&r[16..])?;
                if r[12] as usize != end - start
                    || r[15] as usize != count
                    || r[24] as usize + r[25] as usize != count
                {
                    return None;
                }
                if state == seed {
                    cost = cost.add(Cost {
                        loss: r[8] as u64,
                        base: r[9] as u64,
                        returns: r[10] as u64,
                        operations: r[11] as u64,
                    })?;
                    state = endpoint;
                    true
                } else {
                    false
                }
            } else {
                false
            };
            if !accepted {
                Self::fold_rows(
                    links,
                    index * FOLD,
                    count,
                    words,
                    bits,
                    &mut state,
                    &mut cost,
                )?;
            }
        }
        state.close(&mut cost)?;
        let extra = (128 - (2 * cost.operations as u128).leading_zeros()) as u64;
        let required = cost
            .loss
            .checked_add((bits as u64).max(extra))?
            .checked_add(5)?;
        if required > width {
            return None;
        }
        let result = Summary {
            head: state.head,
            word: (0..state.len)
                .map(|i| 1 + 2 * ((state.word >> i) & 1) as u8)
                .collect(),
            value: u64::try_from(state.b).ok()?,
            loss: cost.loss,
            base: cost.base,
            returns: cost.returns,
            operations: cost.operations,
        };
        result.mode();
        Some(result)
    }

    fn link_endpoint(r: &[u32], length: usize) -> Option<Option<Prefix>> {
        if r[13] > 1 || r[14] > 1 || r[13] > r[14] {
            return None;
        }
        if r[14] == 0 {
            return Some(None);
        }
        if r[12] as usize != length {
            return None;
        }
        Some(Some(Self::row_prefix(r)?))
    }

    fn fold_rows(
        rows: &[u32],
        begin: usize,
        count: usize,
        words: &[u64],
        bits: usize,
        state: &mut Prefix,
        cost: &mut Cost,
    ) -> Option<()> {
        let mut previous = if begin == 0 {
            Some(*state)
        } else {
            Self::link_endpoint(&rows[16 * (begin - 1)..16 * begin], BLOCK)?
        };
        for index in begin..begin + count {
            let row = &rows[16 * index..16 * (index + 1)];
            let start = index * BLOCK;
            let length = (bits - 1 - start).min(BLOCK);
            let endpoint = Self::link_endpoint(row, length)?;
            if row[13] == 1 && previous == Some(*state) {
                *state = endpoint?;
                *cost = cost.add(Cost {
                    loss: row[8] as u64,
                    base: row[9] as u64,
                    returns: row[10] as u64,
                    operations: row[11] as u64,
                })?;
            } else {
                Self::repair(words, start, start + length, state, cost)?;
            }
            previous = endpoint;
        }
        Some(())
    }

    fn row_prefix(r: &[u32]) -> Option<Prefix> {
        if r[4] > 4 || r[5] > 63 || r[6] > 56 {
            return None;
        }
        let state = Prefix {
            word: r[0] as u128 | ((r[1] as u128) << 32),
            b: r[2] as u128 | ((r[3] as u128) << 32),
            head: r[4] as u8,
            len: r[5] as u8,
            k: r[6] as u8,
        };
        (state.valid() && state.b < (1u128 << 60)).then_some(state)
    }

    fn repair(
        words: &[u64],
        start: usize,
        end: usize,
        state: &mut Prefix,
        cost: &mut Cost,
    ) -> Option<()> {
        let mut at = start;
        while at < end {
            let count = (end - at).min(64);
            let shift = at % 64;
            let i = at / 64;
            let mut low = words[i] >> shift;
            if shift != 0 {
                low |= words.get(i + 1).copied().unwrap_or(0) << (64 - shift);
            }
            if count < 64 {
                low &= (1u64 << count) - 1;
            }
            state.feed(low, count as u8, cost)?;
            at += count;
        }
        Some(())
    }
}
