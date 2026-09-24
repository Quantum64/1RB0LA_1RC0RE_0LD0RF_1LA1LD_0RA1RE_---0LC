use crate::normalizer::Summary;
use std::collections::VecDeque;
struct Bits {
    words: Vec<u32>,
    offset: usize,
    top: usize,
}

impl Bits {
    fn from_words(source: &[u64]) -> Self {
        let mut words: Vec<u32> = source
            .iter()
            .flat_map(|x| [*x as u32, (*x >> 32) as u32])
            .collect();
        while words.last() == Some(&0) {
            words.pop();
        }
        assert!(!words.is_empty(), "positive register required");
        let top = 32 * (words.len() - 1) + (32 - words.last().unwrap().leading_zeros()) as usize;
        Self {
            words,
            offset: 0,
            top,
        }
    }
    fn length(&self) -> usize {
        self.top - self.offset
    }

    fn low(&self) -> u32 {
        let at = self.offset / 32;
        let shift = self.offset % 32;
        let mut value = self.words.get(at).copied().unwrap_or(0) >> shift;
        if shift > 0 {
            value |= self.words.get(at + 1).copied().unwrap_or(0) << (32 - shift);
        }
        value
    }

    fn small(&self, n: u32) -> bool {
        self.length() <= 32 && self.low() == n
    }

    fn add_at(&mut self, value: u32, relative_bit: usize) {
        let position = self
            .offset
            .checked_add(relative_bit)
            .expect("bit offset overflow");
        let mut at = position / 32;
        let mut carry = (value as u64) << (position % 32);
        while carry > 0 {
            while self.words.len() <= at {
                self.words.push(0);
            }
            let sum = self.words[at] as u64 + carry;
            self.words[at] = sum as u32;
            carry = sum >> 32;
            at += 1;
        }
        self.top = 32 * (self.words.len() - 1)
            + (32 - self.words.last().unwrap().leading_zeros()) as usize;
    }

    fn shift(&mut self, count: usize) {
        self.offset = self.offset.checked_add(count).expect("bit offset overflow");
        assert!(self.offset < self.top, "positive register became zero");
    }

    fn low_bit(&self) -> usize {
        let first = self.offset / 32;
        let shift = self.offset % 32;
        let low = self.words[first] >> shift;
        if low != 0 {
            return low.trailing_zeros() as usize;
        }
        let mut at = first + 1;
        while self.words[at] == 0 {
            at += 1;
        }
        32 * at + self.words[at].trailing_zeros() as usize - self.offset
    }
}

pub fn normalize(input: &[u64], head: u8, word: &[u8], width: u64) -> Summary {
    run::<false>(input, head, word, width)
}
fn run<const ONE: bool>(input: &[u64], mut head: u8, word: &[u8], width: u64) -> Summary {
    assert!(head <= 4 && word.iter().all(|d| matches!(d, 1 | 3)));
    let mut odd: VecDeque<u8> = word.iter().copied().collect();
    let mut ones = odd.iter().filter(|&&x| x == 1).count();
    let mut value = Bits::from_words(input);
    let (mut loss, mut base, mut returns, mut operations) = (0u64, 0u64, 0u64, 0u64);
    loop {
        if !ONE
            && odd.is_empty()
            && ((head == 2 && value.small(2))
                || (head == 0 && value.small(4))
                || (head == 1 && value.small(3)))
        {
            break;
        }
        if !ONE && head == 1 && !odd.is_empty() && ones == 0 && value.small(1) {
            break;
        }
        let required = loss
            .checked_add(value.length() as u64)
            .unwrap()
            .checked_add(4)
            .unwrap();
        assert!(required <= width, "insufficient actual padding lower bound");
        operations = operations.checked_add(1).unwrap();
        let r = (value.low() & 3) as u8;
        let nonempty = !odd.is_empty();
        let first = odd.front().copied().unwrap_or(3);
        let tail_base = match head {
            0 | 2 => {
                if nonempty {
                    3
                } else {
                    2 + (r % 2) as u64
                }
            }
            1 | 3 => 2 + (r == 2) as u64,
            4 if nonempty && first == 1 => {
                if r % 2 == 1 {
                    6
                } else {
                    3 + (r == 2) as u64
                }
            }
            _ => 6 - (r == 3) as u64,
        };
        base = base.checked_add(tail_base).unwrap();
        returns = returns.checked_add(1).unwrap();
        let mut pop = false;
        let mut append = [0u8; 2];
        let appended: usize;
        match head {
            0 | 2 => {
                if nonempty {
                    head = first + (head == 0) as u8;
                    pop = true;
                    value.add_at(1, 0);
                } else {
                    head = (if head == 0 { 3 } else { 2 }) - 2 * (r % 2);
                    value.add_at(1, 0);
                    value.shift(1);
                    loss += 1;
                }
                appended = 0;
            }
            1 | 3 => {
                if r % 2 == 1 {
                    head -= 1;
                    value.add_at(1, 0);
                    appended = 0;
                } else {
                    head = first + (head == 1) as u8;
                    pop = nonempty;
                    if nonempty {
                        append[0] = 3;
                        append[1] = 3 - r;
                        appended = 2;
                    } else {
                        append[0] = 3 - r;
                        appended = 1;
                    }
                    value.add_at(3, 0);
                    value.shift(2);
                    loss += 2;
                }
            }
            _ if nonempty && first == 1 => {
                head = 3;
                pop = true;
                if r % 2 == 1 {
                    value.add_at(2, 0);
                    appended = 0;
                } else {
                    append = [3, 3 - r];
                    appended = 2;
                    value.add_at(3, 0);
                    value.shift(2);
                    loss += 2;
                    returns += (r == 2) as u64;
                }
            }
            _ => {
                head = 1;
                pop = nonempty;
                let last = if r == 3 { 3 } else { 1 };
                if nonempty {
                    append = [3, last];
                    appended = 2;
                } else {
                    append[0] = last;
                    appended = 1;
                }
                if r % 2 == 1 {
                    value.add_at(3, 0);
                    value.shift(2);
                } else if r == 2 {
                    value.add_at(8, 0);
                    value.shift(2);
                    returns += 1;
                } else {
                    let bit = value.low_bit();
                    assert!(bit >= 2);
                    value.add_at(3, bit);
                    value.shift(2);
                }
                loss += 2;
            }
        }
        if pop {
            if odd.pop_front() == Some(1) {
                ones -= 1;
            }
        }
        for &digit in &append[..appended] {
            odd.push_back(digit);
            ones += (digit == 1) as usize;
        }
        if ONE {
            break;
        }
    }
    assert!(value.length() <= if ONE { 32 } else { 3 });
    Summary {
        head,
        word: odd.into_iter().collect(),
        value: value.low() as u64,
        loss,
        base,
        returns,
        operations,
    }
}
