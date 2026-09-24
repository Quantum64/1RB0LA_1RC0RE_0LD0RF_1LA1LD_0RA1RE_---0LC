use crate::prefix::{Cost, Prefix};
use std::collections::BTreeMap;

fn encode(s: Prefix) -> u64 {
    assert!(s.valid() && s.len < 24 && s.k < 32 && s.b < (1 << 27));
    s.word as u64
        | ((s.len as u64) << 24)
        | ((s.head as u64) << 29)
        | ((s.k as u64) << 32)
        | ((s.b as u64) << 37)
}
fn hash(key: u64) -> u32 {
    let mut x = key as u32 ^ ((key >> 32) as u32).wrapping_mul(0x9e3779b9);
    x ^= x >> 16;
    x = x.wrapping_mul(0x7feb352d);
    x ^= x >> 15;
    x
}
fn potential(s: Prefix) -> i64 {
    (s.head / 2 + 2 * (s.head % 2)) as i64 + 4 * s.len as i64 + s.word.count_ones() as i64
}
pub fn derive() -> Vec<u8> {
    let mut states = vec![
        Prefix::empty(),
        Prefix {
            head: 1,
            word: 1,
            len: 1,
            k: 0,
            b: 0,
        },
    ];
    let mut ids = BTreeMap::new();
    for (i, s) in states.iter().enumerate() {
        ids.insert(encode(*s), i as u32);
    }
    let mut escapes = vec![];
    let mut escape_ids = BTreeMap::new();
    let mut edges = vec![];
    let mut at = 0;
    while at < states.len() {
        let source = states[at];
        for low in 0..256 {
            let mut target = source;
            let mut cost = Cost::default();
            target
                .feed(low, 8, &mut cost)
                .expect("byte derivation exceeded prefix bounds");
            assert_eq!(cost.loss, 8 + source.k as u64 - target.k as u64);
            let id = if target.len <= 14 && target.k <= 8 && target.b <= 64 {
                let next = states.len() as u32;
                *ids.entry(encode(target)).or_insert_with(|| {
                    states.push(target);
                    next
                })
            } else {
                let next = escapes.len() as u32;
                0x80000000
                    | *escape_ids.entry(encode(target)).or_insert_with(|| {
                        escapes.push(target);
                        next
                    })
            };
            let numerator =
                cost.base as i64 - 2 * cost.loss as i64 - potential(source) + potential(target);
            assert!(numerator >= 0 && numerator % 3 == 0);
            let j = numerator as u32 / 3;
            assert!(
                j < 64
                    && cost.operations < 64
                    && cost.returns >= cost.operations
                    && cost.returns - cost.operations < 16
            );
            let weight = (j << 16)
                | ((cost.operations as u32) << 22)
                | (((cost.returns - cost.operations) as u32) << 28);
            edges.push((id, weight));
        }
        at += 1;
        assert!(states.len() + escapes.len() < 65535);
    }
    let common = states.len();
    states.extend(escapes);
    let hash_size = (common * 4).next_power_of_two();
    let mut slots = vec![0u32; hash_size];
    let mut max_probe = 0;
    for (i, s) in states[..common].iter().enumerate() {
        let start = hash(encode(*s)) as usize;
        for probe in 0..hash_size {
            let slot = (start + probe) & (hash_size - 1);
            if slots[slot] == 0 {
                slots[slot] = i as u32 + 1;
                max_probe = max_probe.max(probe + 1);
                break;
            }
        }
    }
    let mut bytes = vec![0u8; 64];
    for s in &states {
        bytes.extend(encode(*s).to_le_bytes());
    }
    let hash_offset = bytes.len() / 4;
    for slot in slots {
        bytes.extend(slot.to_le_bytes());
    }
    assert_eq!(bytes.len() % 8, 0);
    let row_offset = bytes.len() / 8;
    for (id, weight) in edges {
        let endpoint = if id & 0x80000000 == 0 {
            id
        } else {
            common as u32 + (id & 0x7fffffff)
        };
        assert!(endpoint < 65535);
        bytes.extend((endpoint | weight).to_le_bytes());
    }
    let header = [
        0x42544641,
        2,
        common as u32,
        states.len() as u32,
        hash_size as u32,
        8,
        8,
        hash_offset as u32,
        row_offset as u32,
        14,
        max_probe as u32,
        32,
        1,
        16,
        0,
        0,
    ];
    for (i, x) in header.iter().enumerate() {
        bytes[4 * i..4 * i + 4].copy_from_slice(&x.to_le_bytes());
    }
    bytes
}
