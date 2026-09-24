use crate::big::Big;
use std::cmp::Ordering;
const PRECISION: u64 = 256;

pub struct Metadata<'a> {
    pub root: &'a Big,
    pub bits: usize,
    low: Big,
    top: Big,
    mod3: u64,
}
impl<'a> Metadata<'a> {
    pub fn new(root: &'a Big) -> Self {
        assert!(root.sign() > 0);
        let bits = root.bits();
        Self {
            root,
            bits,
            low: root.low(PRECISION),
            top: root.shr((bits as u64).saturating_sub(PRECISION)),
            mod3: root.mod_u(3),
        }
    }
    pub fn residue(&self, modulus: &Big) -> Big {
        assert!(modulus.sign() > 0);
        if modulus.as_u64() == Some(1) {
            return Big::new();
        }
        let binary = modulus.valuation();
        let odd = modulus.shr(binary);
        if binary <= PRECISION && matches!(odd.as_u64(), Some(1 | 3)) {
            let low = self.low.low(binary);
            if odd.as_u64() == Some(1) {
                return low;
            }
            let inverse = if binary % 2 == 0 { 1 } else { 2 };
            let adjustment = ((self.mod3 + 3 - low.mod_u(3)) * inverse) % 3;
            return low.add(&Big::u(adjustment).shl(binary));
        }
        self.root.modulo(modulus)
    }
    pub fn compare_root(&self, value: &Big) -> Ordering {
        if value.sign() < 0 {
            return Ordering::Greater;
        }
        if self.bits != value.bits() {
            return self.bits.cmp(&value.bits());
        }
        if self.bits as u64 <= PRECISION {
            return self.low.cmp(value);
        }
        let top = value.shr(self.bits as u64 - PRECISION);
        let order = self.top.cmp(&top);
        if order != Ordering::Equal {
            return order;
        }
        self.root.cmp(value)
    }
    fn linear_sign(&self, a: &Big, c: &Big) -> Ordering {
        if a.sign() == 0 {
            return c.sign().cmp(&0);
        }
        if a.sign() < 0 {
            return self.linear_sign(&a.neg(), &c.neg()).reverse();
        }
        if c.sign() >= 0 {
            return Ordering::Greater;
        }
        let positive = c.neg();
        let quotient = positive.floor(a);
        let order = self.compare_root(&quotient);
        if order == Ordering::Equal && positive.modulo(a).sign() != 0 {
            Ordering::Less
        } else {
            order
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expression {
    pub slope: Big,
    pub constant: Big,
    pub denominator: Big,
}
impl Expression {
    pub fn evaluate_into(&self, root: &Big, output: &mut Big) {
        output.set_expression(root, &self.slope, &self.constant, &self.denominator)
    }
}

#[derive(Clone)]
pub struct Affine<'m, 'r> {
    pub meta: &'m Metadata<'r>,
    pub expression: Expression,
}
impl<'m, 'r> Affine<'m, 'r> {
    pub fn new(meta: &'m Metadata<'r>, a: Big, c: Big, d: Big) -> Self {
        assert!(d.sign() > 0);
        let gcd = a.gcd(&c).gcd(&d);
        Self {
            meta,
            expression: Expression {
                slope: a.exact(&gcd),
                constant: c.exact(&gcd),
                denominator: d.exact(&gcd),
            },
        }
    }
    pub fn root(meta: &'m Metadata<'r>) -> Self {
        Self::new(meta, Big::i(1), Big::new(), Big::i(1))
    }
    pub fn constant(meta: &'m Metadata<'r>, value: Big) -> Self {
        Self::new(meta, Big::new(), value, Big::i(1))
    }
    pub fn add(&self, other: &Self) -> Self {
        assert!(std::ptr::eq(self.meta, other.meta));
        let a = &self.expression;
        let b = &other.expression;
        Self::new(
            self.meta,
            a.slope
                .mul(&b.denominator)
                .add(&b.slope.mul(&a.denominator)),
            a.constant
                .mul(&b.denominator)
                .add(&b.constant.mul(&a.denominator)),
            a.denominator.mul(&b.denominator),
        )
    }
    pub fn add_big(&self, n: &Big) -> Self {
        let e = &self.expression;
        Self::new(
            self.meta,
            e.slope.clone(),
            e.constant.add(&n.mul(&e.denominator)),
            e.denominator.clone(),
        )
    }
    pub fn add_i(&self, n: i64) -> Self {
        self.add_big(&Big::i(n))
    }
    pub fn sub(&self, other: &Self) -> Self {
        self.add(&other.mul_i(-1))
    }
    pub fn mul_big(&self, n: &Big) -> Self {
        let e = &self.expression;
        Self::new(
            self.meta,
            e.slope.mul(n),
            e.constant.mul(n),
            e.denominator.clone(),
        )
    }
    pub fn mul_i(&self, n: i64) -> Self {
        self.mul_big(&Big::i(n))
    }
    pub fn residue(&self, modulus: &Big) -> Big {
        assert!(modulus.sign() > 0);
        let e = &self.expression;
        let combined = e.denominator.mul(modulus);
        let needed = combined.exact(&e.slope.gcd(&combined));
        let root = self.meta.residue(&needed);
        e.slope
            .mul(&root)
            .add(&e.constant)
            .modulo(&combined)
            .exact(&e.denominator)
    }
    pub fn mod_u(&self, modulus: u64) -> u64 {
        self.residue(&Big::u(modulus)).as_u64().unwrap()
    }
    pub fn floor(&self, divisor: &Big) -> Self {
        let remainder = self.residue(divisor);
        let e = &self.expression;
        Self::new(
            self.meta,
            e.slope.clone(),
            e.constant.sub(&remainder.mul(&e.denominator)),
            e.denominator.mul(divisor),
        )
    }
    pub fn div_u(&self, divisor: u64) -> Self {
        self.floor(&Big::u(divisor))
    }
    pub fn shr(&self, bits: u64) -> Self {
        self.floor(&Big::u(1).shl(bits))
    }
    pub fn cmp(&self, other: &Self) -> Ordering {
        let delta = self.sub(other);
        self.meta
            .linear_sign(&delta.expression.slope, &delta.expression.constant)
    }
    pub fn cmp_big(&self, n: &Big) -> Ordering {
        let e = &self.expression;
        self.meta
            .linear_sign(&e.slope, &e.constant.sub(&e.denominator.mul(n)))
    }
    pub fn ge_i(&self, n: i64) -> bool {
        self.cmp_big(&Big::i(n)) != Ordering::Less
    }
    pub fn ge(&self, other: &Self) -> bool {
        self.cmp(other) != Ordering::Less
    }
    pub fn valuation(&self) -> u64 {
        assert!(self.cmp_big(&Big::new()) == Ordering::Greater);
        let available = PRECISION.saturating_sub(self.expression.denominator.valuation());
        if available > 0 {
            let low = self.residue(&Big::u(1).shl(available));
            if low.sign() != 0 {
                return low.valuation();
            }
        }
        self.evaluate().valuation()
    }
    pub fn evaluate(&self) -> Big {
        let mut output = Big::new();
        self.expression.evaluate_into(self.meta.root, &mut output);
        output
    }
    pub fn lower_u64(&self) -> u64 {
        assert!(self.ge_i(0));
        if self.cmp_big(&Big::u(u64::MAX)) != Ordering::Less {
            u64::MAX
        } else {
            self.evaluate().as_u64().unwrap()
        }
    }
}

pub fn one<'m, 'r>(b: &Affine<'m, 'r>) -> Affine<'m, 'r> {
    assert!(b.ge_i(40));
    let r = b.mod_u(4);
    if r == 3 {
        b.mul_i(64).add_i(547)
    } else {
        b.mul_i(8).add_i(56 + 3 * r as i64)
    }
}
pub fn zero<'m, 'r>(b: &Affine<'m, 'r>) -> Affine<'m, 'r> {
    assert!(b.ge_i(40));
    if b.mod_u(2) == 0 {
        let x = b.mul_i(7).add_i(20);
        let k = x.valuation();
        assert!(k >= 1);
        let n = x.shr(k).mul_big(&Big::pow(9, k)).add_i(-69);
        assert_eq!(n.mod_u(7), 0);
        return n.div_u(7);
    }
    let x = b.mul_i(721).add_i(1917);
    let k = x.valuation();
    assert!(k >= 1);
    let count = (k - 1) / 3;
    let n = x.shr(3 * count).mul_big(&Big::pow(729, count)).add_i(-1917);
    assert_eq!(n.mod_u(721), 0);
    let b = n.div_u(721);
    match k - 3 * count {
        1 => {
            assert_eq!(b.mod_u(4), 1);
            one(&b.mul_i(9).add_i(13).div_u(2))
        }
        2 => {
            assert_eq!(b.mod_u(8), 7);
            one(&b.mul_i(81).add_i(193).div_u(4))
        }
        3 => {
            assert_eq!(b.mod_u(16), 11);
            b.mul_i(729).add_i(1861).div_u(8)
        }
        _ => unreachable!(),
    }
}
pub fn three<'m, 'r>(b: &Affine<'m, 'r>) -> Affine<'m, 'r> {
    assert!(b.ge_i(40));
    match b.mod_u(4) {
        0 => b.mul_i(9).add_i(94).div_u(2),
        2 => zero(&b.mul_i(9).add_i(108).div_u(2)),
        3 => one(&b.mul_i(9).add_i(101).div_u(2)),
        1 => {
            let b = b.mul_i(9).add_i(87).div_u(2);
            assert_eq!(b.mod_u(2), 0);
            if b.mod_u(4) == 0 {
                b.mul_i(9).add_i(94).div_u(2)
            } else {
                zero(&b.mul_i(9).add_i(108).div_u(2))
            }
        }
        _ => unreachable!(),
    }
}
pub fn to_two<'m, 'r>(a: &Affine<'m, 'r>, b: &Affine<'m, 'r>) -> Affine<'m, 'r> {
    assert!(a.ge_i(0) && b.ge_i(40));
    let b = b.add(&a.div_u(4).mul_i(14));
    match a.mod_u(4) {
        0 => zero(&b),
        1 => one(&b),
        2 => b,
        3 => three(&b),
        _ => unreachable!(),
    }
}
