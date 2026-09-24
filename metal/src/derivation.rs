use crate::normalizer::Mode;
use std::{
    collections::{HashMap, VecDeque},
    ops::{Add, Mul, Sub},
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Linear {
    pub a: i128,
    pub b: i128,
}
fn num(b: i128) -> Linear {
    Linear { a: 0, b }
}
impl Add for Linear {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self {
            a: self.a + rhs.a,
            b: self.b + rhs.b,
        }
    }
}
impl Sub for Linear {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self {
            a: self.a - rhs.a,
            b: self.b - rhs.b,
        }
    }
}
impl Mul<i128> for Linear {
    type Output = Self;
    fn mul(self, rhs: i128) -> Self {
        Self {
            a: self.a * rhs,
            b: self.b * rhs,
        }
    }
}
impl Linear {
    pub fn integer(self) -> i128 {
        assert_eq!(self.a, 0);
        self.b
    }
    pub fn ge(self, rhs: i128) -> bool {
        let minimum = 100 * self.a + self.b - rhs;
        if self.a >= 0 && minimum >= 0 {
            return true;
        }
        if self.a <= 0 && minimum < 0 {
            return false;
        }
        panic!("undecided sign over n >= 100: {self:?} >= {rhs}");
    }
    pub fn div(self, divisor: i128) -> Self {
        assert!(
            divisor > 0 && self.ge(0) && self.a % divisor == 0,
            "symbolic division requires another residue split"
        );
        Self {
            a: self.a / divisor,
            b: self.b.div_euclid(divisor),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Word {
    Digits(Vec<u32>),
    Suffix,
}
#[derive(Clone, Debug)]
struct Block {
    word: Word,
    count: Linear,
}
fn block(word: &[u32], count: Linear) -> Block {
    Block {
        word: Word::Digits(word.to_vec()),
        count,
    }
}
#[derive(Clone, Default)]
struct Stack {
    finite: VecDeque<u32>,
    powers: VecDeque<Block>,
}
type Runs = Vec<(Option<u32>, Linear)>;
fn push_run(out: &mut Runs, digit: Option<u32>, count: Linear) {
    if count == num(0) {
        return;
    }
    if let Some(last) = out.last_mut() {
        if last.0 == digit {
            last.1 = last.1 + count;
            return;
        }
    }
    out.push((digit, count));
}
impl Stack {
    fn pop(&mut self) -> u32 {
        if self.finite.is_empty() {
            let Some(Block { word, count }) = self.powers.pop_front() else {
                return 0;
            };
            let Word::Digits(digits) = word else {
                panic!("attempted to inspect W");
            };
            assert!(count.ge(1));
            self.finite.extend(digits.iter().copied());
            if count != num(1) {
                self.powers.push_front(block(&digits, count - num(1)));
            }
        }
        self.finite.pop_front().unwrap()
    }
    fn near(&self, size: usize) -> Vec<u32> {
        let mut probe = self.clone();
        (0..size).map(|_| probe.pop()).collect()
    }
    fn matches(&self, prefix: &[u32]) -> bool {
        let mut probe = self.clone();
        for &digit in prefix {
            if probe.finite.is_empty()
                && matches!(
                    probe.powers.front(),
                    Some(Block {
                        word: Word::Suffix,
                        ..
                    })
                )
            {
                return false;
            }
            if probe.pop() != digit {
                return false;
            }
        }
        true
    }
    fn prepend(&mut self, parts: Vec<Block>) {
        if !self.finite.is_empty() {
            let digits: Vec<_> = self.finite.drain(..).collect();
            self.powers.push_front(block(&digits, num(1)));
        }
        for part in parts.into_iter().rev() {
            if part.count == num(0) || matches!(&part.word, Word::Digits(w) if w.is_empty()) {
                continue;
            }
            assert!(part.count.ge(1));
            self.powers.push_front(part);
        }
        self.normalize();
    }
    fn normalize(&mut self) {
        let mut out: VecDeque<Block> = VecDeque::new();
        for mut part in self.powers.drain(..) {
            if part.count == num(0) {
                continue;
            }
            if let Word::Digits(word) = &mut part.word {
                if word.is_empty() {
                    continue;
                }
                for size in 1..=word.len() {
                    if word.len() % size == 0
                        && word.iter().enumerate().all(|(i, d)| *d == word[i % size])
                    {
                        part.count = part.count * (word.len() / size) as i128;
                        word.truncate(size);
                        break;
                    }
                }
            }
            if let Some(last) = out.back_mut() {
                if last.word == part.word && part.word != Word::Suffix {
                    last.count = last.count + part.count;
                    continue;
                }
            }
            out.push_back(part);
        }
        while matches!(out.back(), Some(Block { word: Word::Digits(w), .. }) if w.iter().all(|&d| d == 0))
        {
            out.pop_back();
        }
        self.powers = out;
        while self.powers.is_empty() && self.finite.back() == Some(&0) {
            self.finite.pop_back();
        }
    }
    fn empty(&self) -> bool {
        self.finite.iter().all(|&d| d == 0)
            && self
                .powers
                .iter()
                .all(|p| matches!(&p.word, Word::Digits(w) if w.iter().all(|&d| d == 0)))
    }
    fn aligned(&mut self, accept: impl Fn(&[u32]) -> bool) -> Option<Block> {
        let part = self.powers.front()?.clone();
        let Word::Digits(word) = &part.word else {
            return None;
        };
        if self.finite.is_empty() {
            if word.len() % 2 == 0 && accept(word) {
                return self.powers.pop_front();
            }
            let doubled = [word.as_slice(), word.as_slice()].concat();
            if word.len() % 2 == 1 && part.count.ge(2) && accept(&doubled) {
                let q = part.count.div(2);
                self.powers.pop_front();
                if part.count - q * 2 != num(0) {
                    self.powers.push_front(block(word, part.count - q * 2));
                }
                return Some(block(&doubled, q));
            }
        } else if self.finite.len() == 1 && word.len() % 2 == 0 && self.finite.back() == word.last()
        {
            let rotated = [vec![self.finite[0]], word[..word.len() - 1].to_vec()].concat();
            if accept(&rotated) {
                self.powers.pop_front();
                return Some(block(&rotated, part.count));
            }
        }
        None
    }
    fn pairs(&mut self, pair: &[u32; 2]) -> Linear {
        let mut count = num(0);
        while self.matches(pair) {
            if let Some(Block {
                word: Word::Digits(word),
                count: n,
            }) = self.aligned(|w| w.chunks_exact(2).all(|p| p == pair))
            {
                count = count + n * (word.len() / 2) as i128;
            } else {
                self.pop();
                self.pop();
                count = count + num(1);
            }
        }
        count
    }
    fn blocks(&self) -> Vec<Block> {
        let mut parts = vec![block(
            &self.finite.iter().copied().collect::<Vec<_>>(),
            num(1),
        )];
        parts.extend(self.powers.iter().cloned());
        parts
    }
    fn paired(&self) -> bool {
        let mut phase = 0usize;
        for part in self.blocks() {
            let Word::Digits(word) = part.word else {
                if phase != 0 || part.count != num(1) {
                    return false;
                }
                continue;
            };
            if word.len() % 2 == 1 && part.count != num(1) {
                if word.iter().any(|&d| d != 1) {
                    return false;
                }
                let size = part.count * word.len() as i128;
                let rest = (size - size.div(2) * 2).integer();
                assert!((0..=1).contains(&rest));
                phase = (phase + rest as usize) % 2;
            } else if word.len() % 2 == 1 {
                for digit in word {
                    if phase == 1 && digit != 1 {
                        return false;
                    }
                    phase = 1 - phase;
                }
            } else if word.iter().skip(1 - phase).step_by(2).any(|&d| d != 1) {
                return false;
            }
        }
        phase == 0
    }
    fn runs(&self) -> Option<Runs> {
        fn eat(word: &[u32], pending: &mut Option<u32>, out: &mut Runs) -> bool {
            for &digit in word {
                if let Some(first) = pending.take() {
                    if digit != 1 {
                        return false;
                    }
                    push_run(out, Some(first), num(1));
                } else {
                    *pending = Some(digit);
                }
            }
            true
        }
        let mut probe = self.clone();
        if probe.pop() != 0 {
            return None;
        }
        let mut out = vec![];
        let mut pending = None;
        for Block { word, mut count } in probe.blocks() {
            let Word::Digits(word) = word else {
                if pending.is_some() || count != num(1) {
                    return None;
                }
                push_run(&mut out, None, num(1));
                continue;
            };
            if count == num(1) {
                if !eat(&word, &mut pending, &mut out) {
                    return None;
                }
            } else if pending.is_none() && word.len() == 2 && word[1] == 1 {
                push_run(&mut out, Some(word[0]), count);
            } else if word == [1] {
                if pending.is_some() {
                    if !eat(&[1], &mut pending, &mut out) {
                        return None;
                    }
                    count = count - num(1);
                }
                push_run(&mut out, Some(1), count.div(2));
                if count - count.div(2) * 2 != num(0) {
                    pending = Some(1);
                }
            } else if count.a == 0 && word.len() as i128 * count.b <= 4096 {
                for _ in 0..count.integer() {
                    if !eat(&word, &mut pending, &mut out) {
                        return None;
                    }
                }
            } else {
                return None;
            }
        }
        pending.is_none().then_some(out)
    }
}
fn boundary(runs: Runs) -> Stack {
    let mut parts = vec![block(&[0], num(1))];
    parts.extend(runs.into_iter().map(|(d, count)| match d {
        Some(d) => block(&[d, 1], count),
        None => Block {
            word: Word::Suffix,
            count,
        },
    }));
    let mut stack = Stack::default();
    stack.prepend(parts);
    stack
}
fn motif(word: &[u32], mut y: u32) -> (u32, Vec<u32>) {
    let mut output = vec![];
    for pair in word.chunks_exact(2) {
        let (b, a) = (pair[0], pair[1]);
        assert_ne!(y, 1, "HALT selector");
        let mut part = if a == 1 {
            vec![]
        } else {
            [vec![0; (a - 2) as usize], vec![b + 3]].concat()
        };
        if y >= 2 {
            part.extend([0, y - 2]);
        }
        part.extend(output);
        output = part;
        y = if a == 1 { b + 3 } else { 0 };
    }
    (y, output)
}

pub struct GapTape {
    left: Stack,
    right: Stack,
    countdowns: bool,
}
impl GapTape {
    pub fn blank() -> Self {
        Self {
            left: Stack::default(),
            right: Stack::default(),
            countdowns: true,
        }
    }
    fn new(runs: Runs, countdowns: bool) -> Self {
        Self {
            left: boundary(runs),
            right: Stack::default(),
            countdowns,
        }
    }
    pub fn k_shape(&self) -> Option<(Linear, Linear)> {
        if !self.right.empty() || !self.left.matches(&[0, 2, 1, 0, 1, 2, 1]) {
            return None;
        }
        let mut probe = self.left.clone();
        for _ in 0..7 {
            probe.pop();
        }
        let a = probe.pairs(&[0, 1]);
        if [probe.pop(), probe.pop()] != [3, 1] {
            return None;
        }
        let b = probe.pairs(&[2, 1]);
        probe.empty().then_some((a, b))
    }
    fn zero_loop(&mut self) -> bool {
        if !self.countdowns || !self.right.empty() {
            return false;
        }
        let Some(mut runs) = self.left.runs() else {
            return false;
        };
        if runs.len() < 3 {
            return false;
        }
        let (at, period, growth) = if runs[..2] == [(Some(0), num(3)), (Some(2), num(1))]
            || runs[..2] == [(Some(1), num(1)), (Some(2), num(2))]
        {
            (2, 3, 12)
        } else if runs.len() >= 4
            && runs[0] == (Some(1), num(1))
            && runs[1].0 == Some(3)
            && runs[2] == (Some(2), num(1))
        {
            (3, 2, 10)
        } else {
            return false;
        };
        let (digit, zeros) = runs[at];
        if digit != Some(0) || !zeros.ge(period) {
            return false;
        }
        let q = zeros.div(period);
        runs[at].1 = zeros - q * period;
        runs.push((Some(2), q * growth));
        self.left = boundary(runs);
        true
    }
    pub fn advance(&mut self) {
        self.advance_inner();
        self.left.normalize();
        self.right.normalize();
    }
    fn advance_inner(&mut self) {
        if self.zero_loop() {
            return;
        }
        if self.countdowns && self.right.empty() {
            if self.left.matches(&[0, 3, 1]) {
                let mut probe = self.left.clone();
                probe.pop();
                let c = probe.pairs(&[3, 1]);
                let zeros = probe.pairs(&[0, 1]);
                if probe.paired() && c.ge(1) && zeros.ge(2) {
                    let q = zeros.div(2);
                    probe.prepend(vec![
                        block(&[0], num(1)),
                        block(&[3, 1], c + q),
                        block(&[0, 1], zeros - q * 2),
                    ]);
                    probe.powers.push_back(block(&[2, 1], q * 2));
                    self.left = probe;
                    return;
                }
            }
            if self.left.matches(&[0, 2, 1, 0, 1, 2, 1]) {
                let mut probe = self.left.clone();
                for _ in 0..7 {
                    probe.pop();
                }
                let zeros = probe.pairs(&[0, 1]);
                if probe.paired() && zeros.ge(4) {
                    let q = zeros.div(4);
                    probe.prepend(vec![
                        block(&[0, 2, 1, 0, 1, 2, 1], num(1)),
                        block(&[0, 1], zeros - q * 4),
                    ]);
                    probe.powers.push_back(block(&[2, 1], q * 14));
                    self.left = probe;
                    return;
                }
            }
        }
        if self.left.matches(&[2]) && self.right.matches(&[0, 0, 0, 0, 3, 0, 1]) {
            let mut probe = self.left.clone();
            probe.pop();
            let budget = probe.pairs(&[0, 1]);
            if budget.ge(1) {
                probe.prepend(vec![block(&[2], num(1))]);
                self.left = probe;
                for _ in 0..7 {
                    self.right.pop();
                }
                self.right.prepend(vec![
                    block(&[0, 0, 0, 0, 3, 0, 1], num(1)),
                    block(&[0, 1], budget),
                ]);
                return;
            }
        }
        let near = self.right.near(3);
        if self.left.paired() {
            if near[..2] == [0, 3] {
                let mut probe = self.right.clone();
                probe.pop();
                probe.pop();
                let mut budget = num(0);
                loop {
                    if probe.finite.front() == Some(&4) {
                        probe.finite.pop_front();
                        budget = budget + num(1);
                    } else if probe.finite.is_empty()
                        && matches!(probe.powers.front(), Some(Block{word:Word::Digits(w),..}) if w.iter().all(|&d|d==4))
                    {
                        let part = probe.powers.pop_front().unwrap();
                        let Word::Digits(w) = part.word else {
                            unreachable!()
                        };
                        budget = budget + part.count * w.len() as i128;
                    } else {
                        break;
                    }
                }
                if budget.ge(1) {
                    self.left.prepend(vec![block(&[0, 1], budget)]);
                    self.left.powers.push_back(block(&[2, 1], budget));
                    probe.prepend(vec![block(&[0, 3], num(1))]);
                    self.right = probe;
                    return;
                }
            }
            if self.right.empty() || (near[0] == 0 && near[1] >= 2) {
                if !self.right.empty() {
                    self.right.pop();
                    let y = self.right.pop();
                    self.right.prepend(vec![block(&[y - 2], num(1))]);
                }
                self.left.prepend(vec![]);
                self.left.powers.push_back(block(&[2, 1], num(1)));
                self.left.prepend(vec![block(&[0], num(1))]);
                return;
            }
            if near[..2] == [0, 0] && near[2] > 0 {
                self.right.pop();
                self.right.pop();
                let z = self.right.pop();
                self.right.prepend(vec![block(&[0, z - 1], num(1))]);
                self.left.prepend(vec![]);
                self.left.powers.push_back(block(&[2, 1], num(1)));
                return;
            }
        }
        let (x, y) = (near[0], near[1]);
        if x > 0 {
            if let Some(Block {
                word: Word::Digits(w),
                count,
            }) = self
                .right
                .aligned(|w| w.chunks_exact(2).all(|p| p[0] > 0 && p[1] == 0))
            {
                let b = self.left.pop();
                let cycle: Vec<_> = w
                    .chunks_exact(2)
                    .rev()
                    .flat_map(|p| [p[0] - 1, 1])
                    .collect();
                let mut last = cycle.clone();
                *last.last_mut().unwrap() = b + 1;
                self.left.prepend(vec![
                    block(&[0], num(1)),
                    block(&cycle, count - num(1)),
                    block(&last, num(1)),
                ]);
                return;
            }
        } else {
            assert_ne!(y, 1, "HALT selector");
            if let Some(Block {
                word: Word::Digits(w),
                count,
            }) = self
                .left
                .aligned(|w| w.iter().skip(1).step_by(2).all(|&a| a >= 1))
            {
                self.right.pop();
                self.right.pop();
                let (fy, first) = motif(&w, y);
                let (cy, cycle) = motif(&w, fy);
                assert_eq!(fy, cy);
                self.right.prepend(vec![
                    block(&[0, fy], num(1)),
                    block(&cycle, count - num(1)),
                    block(&first, num(1)),
                ]);
                return;
            }
        }
        self.right.pop();
        self.right.pop();
        let b = self.left.pop();
        if x > 0 {
            self.left.prepend(vec![block(
                &if y == 0 {
                    vec![0, x - 1, b + 1]
                } else {
                    vec![x - 1, b + 1]
                },
                num(1),
            )]);
            if y > 0 {
                self.right.prepend(vec![block(&[0, y - 1], num(1))]);
            }
        } else {
            let a = self.left.pop();
            let mut word = vec![0; a as usize];
            word.push(b + 3);
            if y >= 2 {
                word.extend([0, y - 2]);
            }
            self.right.prepend(vec![block(&word, num(1))]);
        }
    }
}
fn prefix(mode: Mode, c: usize) -> Vec<u32> {
    match mode {
        Mode::N202 => vec![2, 0, 2],
        Mode::N0002 => vec![0, 0, 0, 2],
        Mode::N122 => vec![1, 2, 2],
        Mode::H => [vec![1], vec![3; c], vec![2]].concat(),
    }
}
pub fn derive_final(mode: Mode, c: usize, zeros: u64, residue: u64) -> (Linear, Linear) {
    assert!(residue < 24);
    let mut runs: Runs = prefix(mode, c)
        .into_iter()
        .map(|d| (Some(d), num(1)))
        .collect();
    runs.extend([
        (Some(0), num(zeros as i128)),
        (Some(3), num(1)),
        (
            Some(2),
            Linear {
                a: 24,
                b: residue as i128,
            },
        ),
    ]);
    let mut tape = GapTape::new(runs, true);
    for _ in 0..30000 {
        tape.advance();
        if let Some(shape) = tape.k_shape() {
            return shape;
        }
    }
    panic!("final-marker symbolic derivation did not finish");
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Middle {
    pub mode: Mode,
    pub c: usize,
    pub loss: i64,
    pub growth: i64,
}
pub fn derive_middle(mode: Mode, c: usize, zeros: u64) -> Middle {
    let n = Linear { a: 1, b: 0 };
    let mut runs: Runs = prefix(mode, c)
        .into_iter()
        .map(|d| (Some(d), num(1)))
        .collect();
    runs.extend([
        (Some(0), num(zeros as i128)),
        (Some(2), num(1)),
        (Some(3), num(1)),
        (Some(0), n),
        (None, num(1)),
    ]);
    let mut tape = GapTape::new(runs, false);
    for _ in 0..30000 {
        tape.advance();
        if !tape.right.empty() {
            continue;
        }
        let Some(runs) = tape.left.runs() else {
            continue;
        };
        let mut before = vec![];
        let mut at = 0;
        while at < runs.len() && runs[at].0.is_some() && runs[at].1.a == 0 {
            before.extend(std::iter::repeat_n(
                runs[at].0.unwrap(),
                usize::try_from(runs[at].1.b).unwrap(),
            ));
            at += 1;
        }
        let (mode, c) = match before.as_slice() {
            [2, 0, 2] => (Mode::N202, 0),
            [0, 0, 0, 2] => (Mode::N0002, 0),
            [1, 2, 2] => (Mode::N122, 0),
            [1, middle @ .., 2] if !middle.is_empty() && middle.iter().all(|&d| d == 3) => {
                (Mode::H, middle.len())
            }
            _ => continue,
        };
        if at >= runs.len() || runs[at].0 != Some(0) {
            continue;
        }
        let loss = n - runs[at].1;
        let suffix = &runs[at + 1..];
        if loss.a != 0 || loss.b < 0 || suffix.len() != 2 || suffix[0] != (None, num(1)) {
            continue;
        }
        if suffix[1].0 == Some(2) && suffix[1].1.a == 0 && suffix[1].1.b > 0 {
            return Middle {
                mode,
                c,
                loss: i64::try_from(loss.b).unwrap(),
                growth: i64::try_from(suffix[1].1.b).unwrap(),
            };
        }
    }
    panic!("middle-marker symbolic derivation did not finish");
}
#[derive(Default)]
pub struct Tables {
    finals: HashMap<(Mode, usize, u64, u64), (Linear, Linear)>,
    middle: HashMap<(Mode, usize, u64), Middle>,
}
impl Tables {
    pub fn final_row(&mut self, mode: Mode, c: usize, z: u64, r: u64) -> [i64; 4] {
        let (a, b) = *self
            .finals
            .entry((mode, c, z, r))
            .or_insert_with(|| derive_final(mode, c, z, r));
        [a.b, a.a, b.b, b.a].map(|x| i64::try_from(x).unwrap())
    }
    pub fn middle(&mut self, mode: Mode, c: usize, z: u64) -> Middle {
        *self
            .middle
            .entry((mode, c, z))
            .or_insert_with(|| derive_middle(mode, c, z))
    }
}
