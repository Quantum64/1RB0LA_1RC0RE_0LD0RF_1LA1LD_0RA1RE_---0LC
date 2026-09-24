#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Prefix {
    pub head: u8,
    pub word: u128,
    pub len: u8,
    pub k: u8,
    pub b: u128,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Cost {
    pub loss: u64,
    pub base: u64,
    pub returns: u64,
    pub operations: u64,
}

impl Cost {
    pub fn add(self, other: Self) -> Option<Self> {
        Some(Self {
            loss: self.loss.checked_add(other.loss)?,
            base: self.base.checked_add(other.base)?,
            returns: self.returns.checked_add(other.returns)?,
            operations: self.operations.checked_add(other.operations)?,
        })
    }
}

impl Prefix {
    pub fn empty() -> Self {
        Self {
            head: 2,
            word: 0,
            len: 0,
            k: 0,
            b: 0,
        }
    }
    pub fn valid(&self) -> bool {
        self.head <= 4
            && self.len < 128
            && self.k <= 112
            && self.word < (1u128 << self.len)
            && self.b < (1u128 << 120)
    }
    fn terminal(&self) -> bool {
        self.k == 0
            && (if self.len == 0 {
                matches!((self.head, self.b), (2, 2) | (0, 4) | (1, 3))
            } else {
                self.head == 1 && self.b == 1 && self.word == (1u128 << self.len) - 1
            })
    }

    fn scalar(&mut self, cost: &mut Cost, closed: bool) -> Option<bool> {
        if !self.valid() {
            return None;
        }
        let nonempty = self.len != 0;
        let first = if !nonempty || self.word & 1 != 0 {
            3
        } else {
            1
        };
        let r = (self.b & 3) as u8;
        if !closed {
            if (1u128 << self.k) + self.b < 9 {
                return Some(false);
            }
            if self.head == 0 || self.head == 2 {
                if !nonempty && self.k < 1 {
                    return Some(false);
                }
            } else {
                if self.k < 1 {
                    return Some(false);
                }
                if (r % 2 == 0 || self.head == 4 && (!nonempty || first == 3)) && self.k < 2 {
                    return Some(false);
                }
            }
            if self.head == 4
                && (!nonempty || first == 3)
                && r == 0
                && self.b & ((1u128 << self.k) - 1) == 0
            {
                return Some(false);
            }
        } else if self.b == 0 {
            return None;
        }
        let base = match self.head {
            0 | 2 => {
                if nonempty {
                    3
                } else {
                    2 + r % 2
                }
            }
            1 | 3 => 2 + (r == 2) as u8,
            4 if nonempty && first == 1 => {
                if r % 2 == 1 {
                    6
                } else {
                    3 + (r == 2) as u8
                }
            }
            4 => 6 - (r == 3) as u8,
            _ => return None,
        };
        let mut pop = false;
        let mut append = [0u8; 2];
        let count;
        let addition;
        let mut loss = 0u8;
        let mut returns = 1u64;
        match self.head {
            0 | 2 => {
                addition = 1;
                if nonempty {
                    self.head = first + (self.head == 0) as u8;
                    pop = true;
                } else {
                    self.head = (if self.head == 0 { 3 } else { 2 }) - 2 * (r % 2);
                    loss = 1;
                }
                count = 0;
            }
            1 | 3 if r % 2 == 1 => {
                self.head -= 1;
                addition = 1;
                count = 0;
            }
            1 | 3 => {
                self.head = first + (self.head == 1) as u8;
                pop = nonempty;
                if nonempty {
                    append = [3, 3 - r];
                    count = 2;
                } else {
                    append[0] = 3 - r;
                    count = 1;
                }
                addition = 3;
                loss = 2;
            }
            4 if nonempty && first == 1 => {
                self.head = 3;
                pop = true;
                if r % 2 == 1 {
                    addition = 2;
                    count = 0;
                } else {
                    append = [3, 3 - r];
                    count = 2;
                    addition = 3;
                    loss = 2;
                    returns += (r == 2) as u64;
                }
            }
            4 => {
                self.head = 1;
                pop = nonempty;
                let last = if r == 3 { 3 } else { 1 };
                if nonempty {
                    append = [3, last];
                    count = 2;
                } else {
                    append[0] = last;
                    count = 1;
                }
                addition = if r % 2 == 1 {
                    3
                } else if r == 2 {
                    returns += 1;
                    8
                } else {
                    let low = if closed {
                        self.b
                    } else {
                        self.b & ((1u128 << self.k) - 1)
                    };
                    if low == 0 {
                        return None;
                    }
                    3u128.checked_mul(low & low.wrapping_neg())?
                };
                loss = 2;
            }
            _ => return None,
        }
        self.b = self.b.checked_add(addition)? >> loss;
        if !closed {
            self.k = self.k.checked_sub(loss)?;
        }
        if pop {
            self.word >>= 1;
            self.len -= 1;
        }
        for &digit in &append[..count] {
            if self.len >= 127 {
                return None;
            }
            self.word |= ((digit == 3) as u128) << self.len;
            self.len += 1;
        }
        *cost = cost.add(Cost {
            loss: loss as u64,
            base: base as u64,
            returns,
            operations: 1,
        })?;
        Some(true)
    }

    pub fn epsilon(&mut self, cost: &mut Cost) -> Option<()> {
        for _ in 0..1_000_000 {
            if !self.valid() {
                return None;
            }
            if !self.scalar(cost, false)? {
                return Some(());
            }
        }
        None
    }

    pub fn feed(&mut self, low: u64, bits: u8, cost: &mut Cost) -> Option<()> {
        if bits > 64 || self.k as u16 + bits as u16 > 112 {
            return None;
        }
        if bits < 64 && low >= (1u64 << bits) {
            return None;
        }
        self.b = self.b.checked_add((low as u128) << self.k)?;
        self.k += bits;
        self.epsilon(cost)
    }

    pub fn close(&mut self, cost: &mut Cost) -> Option<()> {
        if !self.valid() {
            return None;
        }
        self.b = self.b.checked_add(1u128 << self.k)?;
        self.k = 0;
        for _ in 0..1_000_000 {
            if self.terminal() {
                return Some(());
            }
            if !self.scalar(cost, true)? {
                return None;
            }
        }
        None
    }
}
