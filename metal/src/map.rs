use crate::{
    affine::{to_two, Affine, Metadata},
    big::Big,
    derivation::{GapTape, Tables},
    normalizer::{Mode, Normalizer, Summary},
};
use std::cmp::Ordering;

pub const MINIMUM: u64 = 131072;
#[derive(Clone)]
struct Normal<'m, 'r> {
    mode: Mode,
    c: usize,
    zeros: Affine<'m, 'r>,
    tail: Affine<'m, 'r>,
}
fn zero_remainder<'m, 'r>(state: Normal<'m, 'r>) -> Normal<'m, 'r> {
    let q = state.zeros.div_u(state.mode.period());
    let z = state.zeros.mod_u(state.mode.period());
    Normal {
        zeros: Affine::constant(state.zeros.meta, Big::u(z)),
        tail: state.tail.add(&q.mul_i(state.mode.growth())),
        ..state
    }
}
fn small<'m, 'r>(
    normalizer: &mut Normalizer,
    head: u8,
    word: &[u8],
    v: u64,
    width: Affine<'m, 'r>,
    tail_without_population: Affine<'m, 'r>,
) -> Normal<'m, 'r> {
    let s = normalizer.normalize(&Big::u(v), head, word, width.lower_u64());
    let result = Normal {
        mode: s.mode(),
        c: s.word.len(),
        zeros: width
            .add_big(&Big::u(s.loss).neg())
            .add_i(-((64 - s.value.leading_zeros()) as i64)),
        tail: tail_without_population
            .add_big(&Big::u(s.base))
            .add_i(-(s.value.count_ones() as i64)),
    };
    result
}
fn final_small<'m, 'r>(tables: &mut Tables, state: Normal<'m, 'r>) -> Affine<'m, 'r> {
    let n = state.tail.div_u(24);
    let r = state.tail.mod_u(24);
    assert!(n.ge_i(100));
    let z = state.zeros.evaluate().as_u64().unwrap();
    let [a0, a1, b0, b1] = tables.final_row(state.mode, state.c, z, r);
    let result = to_two(&n.mul_i(a1).add_i(a0), &n.mul_i(b1).add_i(b0));
    assert!(result.ge(&state.tail));
    result
}
fn finish<'m, 'r>(
    tables: &mut Tables,
    normalizer: &mut Normalizer,
    mut state: Normal<'m, 'r>,
) -> (Affine<'m, 'r>, Option<usize>) {
    loop {
        assert!(state.zeros.ge_i(0) && state.tail.ge_i(2400));
        if state.mode == Mode::N202 {
            let result = to_two(&state.zeros, &state.tail);
            assert!(result.ge(&state.tail));
            return (result, None);
        }
        state = zero_remainder(state);
        if state.mode != Mode::H {
            return (final_small(tables, state), None);
        }
        let c = i64::try_from(state.c).unwrap();
        assert!(c >= 2 && c % 2 == 0 && state.tail.ge_i(3 * c + 100));
        if state.zeros.mod_u(2) == 1 {
            if c >= 18 {
                return (state.tail, Some(c as usize));
            }
            return (final_small(tables, state), None);
        }
        if c <= 14 {
            return (final_small(tables, state), None);
        }
        let previous = state.tail.clone();
        state = small(
            normalizer,
            2,
            &[],
            c as u64 / 2 - 1,
            state.tail.add_i(-c - 9),
            state.tail.add_i(10 * c + 58),
        );
        assert_eq!(state.tail.cmp(&previous), Ordering::Greater);
        if state.mode == Mode::H {
            assert!(state.c <= c as usize - 4)
        }
    }
}
pub(crate) fn compile<'m, 'r>(
    tables: &mut Tables,
    normalizer: &mut Normalizer,
    meta: &'m Metadata<'r>,
    first: &Summary,
) -> (Affine<'m, 'r>, Option<usize>) {
    let root = Affine::root(meta);
    assert!(root.ge_i(2));
    let n = root.div_u(2);
    let odd = root.mod_u(2) != 0;
    let width = root.mul_i(2).add_i(18);
    let operation_bits = 128 - (2 * first.operations as u128).leading_zeros();
    let required = Big::u(first.loss).add(&Big::u(
        (meta.bits as u64 + 1).max(operation_bits as u64) + 5,
    ));
    assert!(
        width.cmp_big(&required) != Ordering::Less,
        "insufficient first-register padding"
    );
    let first_normal = Normal {
        mode: first.mode(),
        c: first.word.len(),
        zeros: width
            .add_big(&Big::u(first.loss).neg())
            .add_i(-((64 - first.value.leading_zeros()) as i64)),
        tail: n
            .mul_i(9)
            .add_i(if odd { 48 } else { 51 })
            .add_big(&Big::u(first.base))
            .add_i(-(first.value.count_ones() as i64)),
    };
    let final_normal = if odd {
        let first = zero_remainder(first_normal);
        let width = n.mul_i(4).add_i(19);
        let z = first.zeros.mod_u(first.mode.period());
        if first.mode == Mode::H && first.c >= 10 {
            let c = i64::try_from(first.c).unwrap();
            assert!(z <= 1 && width.ge_i(2 * c + 100));
            let (head, word, v, loss, constant) = if z == 1 && c % 2 == 0 {
                (1, vec![3, 1], c / 2 - 1, c + 5, 41)
            } else if z == 1 {
                (2, vec![], (c + 1) / 2, c + 8, 57)
            } else if c % 2 == 1 {
                (2, vec![], (c + 3) / 2, c + 5, 34)
            } else {
                (2, vec![], c / 2 + 2, c + 2, 25)
            };
            small(
                normalizer,
                head,
                &word,
                v as u64,
                width.add_i(-loss),
                first.tail.add_i(10 * c + constant),
            )
        } else {
            let rule = tables.middle(first.mode, first.c, z);
            assert!(width.ge_i(rule.loss));
            Normal {
                mode: rule.mode,
                c: rule.c,
                zeros: width.add_i(-rule.loss),
                tail: first.tail.add_i(rule.growth),
            }
        }
    } else {
        first_normal
    };
    assert!(final_normal.tail.ge(&n.mul_i(8)));
    let (result, halt) = finish(tables, normalizer, final_normal);
    if halt.is_none() {
        assert!(result.ge(&root.mul_i(4).add_i(-4)) && result.ge_i(MINIMUM as i64))
    }
    (result, halt)
}
pub struct Step {
    pub halt_c: Option<usize>,
}
pub struct Engine {
    pub normalizer: Normalizer,
    tables: Tables,
    scratch: Big,
}
impl Engine {
    pub fn new() -> Result<Self, String> {
        Ok(Self {
            normalizer: Normalizer::new()?,
            tables: Tables::default(),
            scratch: Big::new(),
        })
    }
    pub fn step(&mut self, root: &Big, output: &mut Big) -> Step {
        assert!(root.cmp(&Big::u(2)) != Ordering::Less);
        let width = root
            .as_u64()
            .and_then(|v| v.checked_mul(2))
            .and_then(|v| v.checked_add(18))
            .unwrap_or(u64::MAX);
        let first = self
            .normalizer
            .normalize_entry(root, &mut self.scratch, width);
        let metadata = Metadata::new(root);
        let (affine, halt_c) = compile(&mut self.tables, &mut self.normalizer, &metadata, &first);
        affine.expression.evaluate_into(root, output);
        Step { halt_c }
    }
    pub fn blank_seed(&mut self) -> Big {
        let mut tape = GapTape::blank();
        let (a, b) = loop {
            tape.advance();
            if let Some((a, b)) = tape.k_shape() {
                if b.integer() >= 40 {
                    break (a.integer(), b.integer());
                }
            }
        };
        let dummy = Big::u(1);
        let meta = Metadata::new(&dummy);
        let mut b = to_two(
            &Affine::constant(&meta, Big::u(u64::try_from(a).unwrap())),
            &Affine::constant(&meta, Big::u(u64::try_from(b).unwrap())),
        )
        .evaluate();
        let mut next = Big::new();
        while b.cmp(&Big::u(MINIMUM)) == Ordering::Less {
            assert!(
                self.step(&b, &mut next).halt_c.is_none(),
                "halt during blank bootstrap"
            );
            std::mem::swap(&mut b, &mut next);
        }
        b
    }
}
