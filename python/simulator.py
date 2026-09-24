import argparse
from dataclasses import dataclass
from functools import lru_cache

from derivation import GapTape, derive_final, derive_middle, evaluate

MINIMUM = 131072
PERIOD = {"202": 4, "0002": 3, "122": 3, "H": 2}
GROWTH = {"202": 14, "0002": 12, "122": 12, "H": 10}


@dataclass(frozen=True)
class Register:
    head: int
    word: tuple
    value: int
    width: int

    def mode(self):
        if not self.word:
            return {(2, 2): "202", (0, 4): "0002", (1, 3): "122"}.get(
                (self.head, self.value)
            )
        if self.head == self.value == 1 and all(d == 3 for d in self.word):
            return "H"
        return None

    def advance(self):
        h, u, v, n = self.head, self.word, self.value, self.width
        if h not in range(5) or v <= 0 or any(d not in (1, 3) for d in u):
            raise ValueError("invalid positive register")
        if n < v.bit_length() + 4:
            raise ValueError("register equation requires four padding zeros")
        first, rest = (u[0], u[1:]) if u else (3, ())
        r = v % 4
        if h in (0, 2):
            if u:
                return Register(first + (h == 0), rest, v + 1, n), 3, 1
            return (
                Register((3 if h == 0 else 2) - 2 * (r % 2), (), (v + 1) // 2, n - 1),
                2 + r % 2,
                1,
            )
        if h in (1, 3):
            if r % 2:
                return Register(h - 1, u, v + 1, n), 2, 1
            word = rest + ((3,) if u else ()) + (3 - r,)
            return (
                Register(first + (h == 1), word, (v + 3) // 4, n - 2),
                2 + (r == 2),
                1,
            )
        if u and first == 1:
            if r % 2:
                return Register(3, rest, v + 2, n), 6, 1
            return (
                Register(3, rest + (3, 3 - r), (v + 3) // 4, n - 2),
                3 + (r == 2),
                1 + (r == 2),
            )
        word = rest + ((3,) if u else ()) + (3 if r == 3 else 1,)
        if r % 2:
            value = (v + 3) // 4
        elif r == 2:
            value = v // 4 + 2
        else:
            value = (v + 3 * (v & -v)) // 4
        return Register(1, word, value, n - 2), 6 - (r == 3), 1 + (r == 2)


def normalize(state):
    base = returns = equations = 0
    while state.mode() is None:
        state, extra, count = state.advance()
        base += extra
        returns += count
        equations += 1
    return state, base, returns, equations


@dataclass(frozen=True)
class Normal:
    mode: str
    c: int
    zeros: int
    tail: int


@dataclass(frozen=True)
class Halt:
    c: int
    tail: int


def normal(head, word, value, width, tail_without_population):
    state, base, _, _ = normalize(Register(head, word, value, width))
    return Normal(
        state.mode(),
        len(state.word),
        state.width - state.value.bit_length(),
        tail_without_population + base - bin(state.value).count("1"),
    )


def valuation(x):
    assert x > 0
    return (x & -x).bit_length() - 1


def k_one(b):
    return 64 * b + 547 if b % 4 == 3 else 8 * b + 56 + 3 * (b % 4)


def k_zero(b):
    if b % 2 == 0:
        x = 7 * b + 20
        k = valuation(x)
        return (9**k * (x >> k) - 69) // 7
    x = 721 * b + 1917
    k = valuation(x)
    count = (k - 1) // 3
    b = (729**count * (x >> (3 * count)) - 1917) // 721
    residue = k - 3 * count
    if residue == 1:
        return k_one((9 * b + 13) // 2)
    if residue == 2:
        return k_one((81 * b + 193) // 4)
    return (729 * b + 1861) // 8


def k_three(b):
    r = b % 4
    if r == 0:
        return (9 * b + 94) // 2
    if r == 2:
        return k_zero((9 * b + 108) // 2)
    if r == 3:
        return k_one((9 * b + 101) // 2)
    b = (9 * b + 87) // 2
    return (9 * b + 94) // 2 if b % 4 == 0 else k_zero((9 * b + 108) // 2)


def to_two(a, b):
    assert a >= 0 and b >= 40
    q, a = divmod(a, 4)
    b += 14 * q
    return (k_zero, k_one, lambda x: x, k_three)[a](b)


def zero_remainder(state):
    q, zeros = divmod(state.zeros, PERIOD[state.mode])
    return Normal(state.mode, state.c, zeros, state.tail + GROWTH[state.mode] * q)


def final_small(state):
    mode, c, z = state.mode, state.c, state.zeros
    if mode in ("0002", "122"):
        assert c == 0 and 0 <= z < 3
    else:
        assert mode == "H" and z in (0, 1) and c % 2 == 0
        assert 2 <= c <= (16 if z else 14)
    n, r = divmod(state.tail, 24)
    assert n >= 100
    a, b = derive_final(mode, c, z, r)
    return to_two(evaluate(a, n), evaluate(b, n))


def finish(state):
    while True:
        assert state.zeros >= 0 and state.tail >= 2400
        if state.mode == "202":
            return to_two(state.zeros, state.tail)
        state = zero_remainder(state)
        if state.mode != "H":
            return final_small(state)
        c, tail = state.c, state.tail
        assert c >= 2 and c % 2 == 0 and tail >= 3 * c + 100
        if state.zeros == 1:
            return Halt(c, tail) if c >= 18 else final_small(state)
        if c <= 14:
            return final_small(state)
        state = normal(2, (), c // 2 - 1, tail - c - 9, tail + 10 * c + 58)
        assert state.tail > tail and (state.mode != "H" or state.c <= c - 4)


def step(b):
    if b < MINIMUM:
        raise ValueError(f"the complete return rules require b >= {MINIMUM}")
    return return_map(b)


def return_map(b):
    assert b >= 2
    n, odd = divmod(b, 2)
    if not odd:
        state = normal(2, (), n + 6, 4 * n + 18, 9 * n + 51)
    else:
        state = zero_remainder(normal(1, (3,), 2 * n + 11, 4 * n + 20, 9 * n + 48))
        width = 4 * n + 19
        c, z = state.c, state.zeros
        if state.mode == "H" and c >= 10:
            assert width >= 2 * c + 100
            if z == 1 and c % 2 == 0:
                h, u, v, loss, extra = 1, (3, 1), c // 2 - 1, c + 5, 41
            elif z == 1:
                h, u, v, loss, extra = 2, (), (c + 1) // 2, c + 8, 57
            elif c % 2:
                h, u, v, loss, extra = 2, (), (c + 3) // 2, c + 5, 34
            else:
                h, u, v, loss, extra = 2, (), c // 2 + 2, c + 2, 25
            state = normal(h, u, v, width - loss, state.tail + 10 * c + extra)
        else:
            mode, c, loss, extra = derive_middle(state.mode, c, z)
            assert width >= loss
            state = Normal(mode, c, width - loss, state.tail + extra)
    assert state.tail >= 8 * n
    result = finish(state)
    assert isinstance(result, Halt) or result >= 4 * b - 4
    return result


@lru_cache(None)
def blank_seed():
    tape = GapTape()
    while True:
        tape.advance()
        shape = tape.k_shape()
        if shape is not None and shape[1] >= 40:
            b = to_two(*shape)
            while b < MINIMUM:
                b = return_map(b)
                if isinstance(b, Halt):
                    return b
            return b


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--b",
        type=lambda s: int(s, 0),
        help="start at K(2,B), decimal or 0x...; default derives the blank prefix",
    )
    parser.add_argument(
        "--returns", type=int, default=10, help="maximum complete returns"
    )
    args = parser.parse_args()
    if (args.b is not None and args.b < MINIMUM) or args.returns < 0:
        parser.error("require B >= 131072 and a nonnegative return limit")
    b = blank_seed() if args.b is None else args.b
    if isinstance(b, Halt):
        print(b)
        return
    describe = lambda x: str(x) if x.bit_length() <= 200 else f"<{x.bit_length()} bits>"
    print(f"0: K(2,{describe(b)})")
    for i in range(1, args.returns + 1):
        result = step(b)
        if isinstance(result, Halt):
            print(
                f"halt on invocation {i}: H({result.c},1,{describe(result.tail)}) -> F/0"
            )
            return
        b = result
        print(f"{i}: K(2,{describe(b)})")
    print("Return limit reached.")


if __name__ == "__main__":
    main()
