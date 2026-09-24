from collections import deque
from dataclasses import dataclass
from functools import lru_cache


@dataclass(frozen=True, eq=False)
class Linear:
    a: int
    b: int = 0

    @staticmethod
    def make(a, b):
        return Linear(a, b) if a else b

    def __add__(self, other):
        other = other if isinstance(other, Linear) else Linear(0, other)
        return self.make(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return self.make(-self.a, -self.b)

    def __sub__(self, other):
        return self + -other

    def __rsub__(self, other):
        return other + -self

    def __mul__(self, integer):
        assert isinstance(integer, int), "only affine tape counts are supported"
        return self.make(self.a * integer, self.b * integer)

    __rmul__ = __mul__

    def __eq__(self, other):
        other = other if isinstance(other, Linear) else Linear(0, other)
        return (self.a, self.b) == (other.a, other.b)

    def __ge__(self, other):
        delta = self - other
        if isinstance(delta, int):
            return delta >= 0
        minimum = 100 * delta.a + delta.b
        if delta.a >= 0 and minimum >= 0:
            return True
        if delta.a <= 0 and minimum < 0:
            return False
        raise ValueError(f"undecided sign over n>=100: {delta}")

    def __gt__(self, other):
        return self >= other + 1

    def __lt__(self, other):
        return -self > -other

    def __floordiv__(self, divisor):
        if not self >= 0 or self.a % divisor:
            raise ValueError("a symbolic division requires another residue split")
        return self.make(self.a // divisor, self.b // divisor)


def evaluate(value, n):
    return value.a * n + value.b if isinstance(value, Linear) else value


class Stack:
    def __init__(self, finite=(), powers=()):
        self.finite, self.powers = deque(finite), deque(powers)

    def copy(self):
        return Stack(self.finite, self.powers)

    def pop(self):
        if not self.finite:
            if not self.powers:
                return 0
            word, count = self.powers.popleft()
            if word == "W":
                raise ValueError("attempted to inspect the arbitrary suffix")
            assert count > 0
            self.finite.extend(word)
            if count != 1:
                self.powers.appendleft((word, count - 1))
        return self.finite.popleft()

    def near(self, size):
        probe = self.copy()
        return [probe.pop() for _ in range(size)]

    def matches(self, prefix):
        probe = self.copy()
        for digit in prefix:
            if not probe.finite and probe.powers and probe.powers[0][0] == "W":
                return False
            if probe.pop() != digit:
                return False
        return True

    def prepend(self, parts):
        if self.finite:
            self.powers.appendleft((tuple(self.finite), 1))
            self.finite.clear()
        for word, count in reversed(parts):
            if word and count != 0:
                assert count > 0
                self.powers.appendleft((word if word == "W" else tuple(word), count))
        self.normalize()

    def normalize(self):
        out = deque()
        for word, count in self.powers:
            if not word or count == 0:
                continue
            if word != "W":
                for size in range(1, len(word) + 1):
                    if len(word) % size == 0 and word == word[:size] * (
                        len(word) // size
                    ):
                        count, word = count * (len(word) // size), word[:size]
                        break
            if out and out[-1][0] == word and word != "W":
                count += out.pop()[1]
            out.append((word, count))
        while out and all(d == 0 for d in out[-1][0]):
            out.pop()
        self.powers = out
        while not out and self.finite and self.finite[-1] == 0:
            self.finite.pop()

    def empty(self):
        return not any(self.finite) and all(not any(w) for w, _ in self.powers)

    def aligned(self, accept):
        if not self.powers or self.powers[0][0] == "W":
            return None
        word, count = self.powers[0]
        if not self.finite:
            if len(word) % 2 == 0 and accept(word):
                return self.powers.popleft()
            if len(word) % 2 and count >= 2 and accept(word + word):
                q = count // 2
                self.powers.popleft()
                if count - 2 * q != 0:
                    self.powers.appendleft((word, count - 2 * q))
                return word + word, q
        elif (
            len(self.finite) == 1 and len(word) % 2 == 0 and self.finite[0] == word[-1]
        ):
            rotated = (self.finite[0],) + word[:-1]
            if accept(rotated):
                self.powers.popleft()
                return rotated, count
        return None

    def pairs(self, pair):
        count = 0
        while self.matches(pair):
            block = self.aligned(
                lambda w: all(w[i : i + 2] == tuple(pair) for i in range(0, len(w), 2))
            )
            if block:
                word, n = block
                count += n * (len(word) // 2)
            else:
                self.pop()
                self.pop()
                count += 1
        return count

    def paired(self):
        phase = 0
        for word, count in [(tuple(self.finite), 1), *self.powers]:
            if word == "W":
                if phase or count != 1:
                    return False
            elif len(word) % 2 and count != 1:
                if any(d != 1 for d in word):
                    return False
                size = len(word) * count
                rest = size - 2 * (size // 2)
                assert rest in (0, 1)
                phase = (phase + rest) % 2
            elif len(word) % 2:
                for digit in word:
                    if phase and digit != 1:
                        return False
                    phase = 1 - phase
            elif any(word[i] != 1 for i in range(1 - phase, len(word), 2)):
                return False
        return phase == 0

    def runs(self):
        probe = self.copy()
        if probe.pop() != 0:
            return None
        out, pending = [], []

        def push(digit, count):
            if count != 0:
                if out and out[-1][0] == digit:
                    count += out.pop()[1]
                out.append((digit, count))

        def eat(word):
            for digit in word:
                pending.append(digit)
                if len(pending) == 2:
                    if pending[1] != 1:
                        return False
                    push(pending[0], 1)
                    pending.clear()
            return True

        if not eat(probe.finite):
            return None
        for word, count in probe.powers:
            if word == "W":
                if pending or count != 1:
                    return None
                push(word, 1)
            elif count == 1:
                if not eat(word):
                    return None
            elif not pending and len(word) == 2 and word[1] == 1:
                push(word[0], count)
            elif word == (1,):
                if pending:
                    if not eat((1,)):
                        return None
                    count -= 1
                push(1, count // 2)
                if count - 2 * (count // 2) != 0:
                    pending.append(1)
            elif isinstance(count, int) and len(word) * count <= 4096:
                if not eat(word * count):
                    return None
            else:
                return None
        return None if pending else out


def boundary(runs):
    stack = Stack()
    stack.prepend([((0,), 1)] + [(d if d == "W" else (d, 1), n) for d, n in runs])
    return stack


def motif(word, y):
    output = ()
    for b, a in zip(word[::2], word[1::2]):
        if y == 1:
            raise ValueError("HALT selector")
        part = () if a == 1 else (0,) * (a - 2) + (b + 3,)
        if y >= 2:
            part += (0, y - 2)
        output = part + output
        y = b + 3 if a == 1 else 0
    return y, output


class GapTape:
    def __init__(self, runs=None, countdowns=True):
        self.left = Stack() if runs is None else boundary(runs)
        self.right = Stack()
        self.countdowns = countdowns

    def k_shape(self):
        if not self.right.empty() or not self.left.matches((0, 2, 1, 0, 1, 2, 1)):
            return None
        probe = self.left.copy()
        for _ in range(7):
            probe.pop()
        a = probe.pairs((0, 1))
        if [probe.pop(), probe.pop()] != [3, 1]:
            return None
        b = probe.pairs((2, 1))
        return (a, b) if probe.empty() else None

    def zero_loop(self):
        if not self.countdowns or not self.right.empty():
            return False
        runs = self.left.runs()
        if runs is None or len(runs) < 3:
            return False
        if runs[:2] in ([(0, 3), (2, 1)], [(1, 1), (2, 2)]):
            at, period, growth = 2, 3, 12
        elif (
            len(runs) >= 4
            and runs[0] == (1, 1)
            and runs[1][0] == 3
            and runs[2] == (2, 1)
        ):
            at, period, growth = 3, 2, 10
        else:
            return False
        digit, zeros = runs[at]
        if digit != 0 or not zeros >= period:
            return False
        q = zeros // period
        self.left = boundary(
            runs[:at] + [(0, zeros - period * q)] + runs[at + 1 :] + [(2, growth * q)]
        )
        return True

    def advance(self):
        self._advance()
        self.left.normalize()
        self.right.normalize()

    def _advance(self):
        if self.zero_loop():
            return
        l, r = self.left, self.right
        if self.countdowns and r.empty():
            if l.matches((0, 3, 1)):
                probe = l.copy()
                probe.pop()
                c, zeros = probe.pairs((3, 1)), probe.pairs((0, 1))
                if probe.paired() and c >= 1 and zeros >= 2:
                    q = zeros // 2
                    probe.prepend([((0,), 1), ((3, 1), c + q), ((0, 1), zeros - 2 * q)])
                    probe.powers.append(((2, 1), 2 * q))
                    self.left = probe
                    return
            if l.matches((0, 2, 1, 0, 1, 2, 1)):
                probe = l.copy()
                for _ in range(7):
                    probe.pop()
                zeros = probe.pairs((0, 1))
                if probe.paired() and zeros >= 4:
                    q = zeros // 4
                    probe.prepend([((0, 2, 1, 0, 1, 2, 1), 1), ((0, 1), zeros - 4 * q)])
                    probe.powers.append(((2, 1), 14 * q))
                    self.left = probe
                    return
        if l.matches((2,)) and r.matches((0, 0, 0, 0, 3, 0, 1)):
            probe = l.copy()
            probe.pop()
            budget = probe.pairs((0, 1))
            if budget > 0:
                probe.prepend([((2,), 1)])
                self.left = probe
                for _ in range(7):
                    r.pop()
                r.prepend([((0, 0, 0, 0, 3, 0, 1), 1), ((0, 1), budget)])
                return
        near = r.near(3)
        if l.paired():
            if near[:2] == [0, 3]:
                probe = r.copy()
                probe.pop()
                probe.pop()
                budget = 0
                while True:
                    if probe.finite and probe.finite[0] == 4:
                        probe.finite.popleft()
                        budget += 1
                    elif (
                        not probe.finite
                        and probe.powers
                        and all(d == 4 for d in probe.powers[0][0])
                    ):
                        word, count = probe.powers.popleft()
                        budget += len(word) * count
                    else:
                        break
                if budget > 0:
                    l.prepend([((0, 1), budget)])
                    l.powers.append(((2, 1), budget))
                    probe.prepend([((0, 3), 1)])
                    self.right = probe
                    return
            if r.empty() or (near[0] == 0 and near[1] >= 2):
                if not r.empty():
                    r.pop()
                    y = r.pop()
                    r.prepend([((y - 2,), 1)])
                l.prepend([])
                l.powers.append(((2, 1), 1))
                l.prepend([((0,), 1)])
                return
            if near[:2] == [0, 0] and near[2] > 0:
                r.pop()
                r.pop()
                z = r.pop()
                r.prepend([((0, z - 1), 1)])
                l.prepend([])
                l.powers.append(((2, 1), 1))
                return
        x, y = near[:2]
        if x > 0:
            block = r.aligned(
                lambda w: all(a > 0 and b == 0 for a, b in zip(w[::2], w[1::2]))
            )
            if block:
                word, count = block
                b = l.pop()
                cycle = tuple(d for a in reversed(word[::2]) for d in (a - 1, 1))
                l.prepend([((0,), 1), (cycle, count - 1), (cycle[:-1] + (b + 1,), 1)])
                return
        else:
            if y == 1:
                raise ValueError("HALT selector")
            block = l.aligned(lambda w: all(a >= 1 for a in w[1::2]))
            if block:
                word, count = block
                r.pop()
                r.pop()
                fy, first = motif(word, y)
                cy, cycle = motif(word, fy)
                assert fy == cy
                r.prepend([((0, fy), 1), (cycle, count - 1), (first, 1)])
                return
        r.pop()
        r.pop()
        b = l.pop()
        if x > 0:
            l.prepend([((0, x - 1, b + 1) if y == 0 else (x - 1, b + 1), 1)])
            if y:
                r.prepend([((0, y - 1), 1)])
        else:
            a = l.pop()
            r.prepend([((0,) * a + (b + 3,) + ((0, y - 2) if y >= 2 else ()), 1)])


def prefix(mode, c):
    return [1] + [3] * c + [2] if mode == "H" else [int(d) for d in mode]


@lru_cache(None)
def derive_final(mode, c, zeros, residue):
    runs = [(d, 1) for d in prefix(mode, c)] + [
        (0, zeros),
        (3, 1),
        (2, Linear(24, residue)),
    ]
    tape = GapTape(runs)
    for _ in range(30000):
        tape.advance()
        shape = tape.k_shape()
        if shape is not None:
            return shape
    raise RuntimeError("final-marker symbolic derivation did not finish")


@lru_cache(None)
def derive_middle(mode, c, zeros):
    n = Linear(1)
    runs = [(d, 1) for d in prefix(mode, c)] + [
        (0, zeros),
        (2, 1),
        (3, 1),
        (0, n),
        ("W", 1),
    ]
    tape = GapTape(runs, countdowns=False)
    for _ in range(30000):
        tape.advance()
        if not tape.right.empty():
            continue
        runs = tape.left.runs()
        if runs is None:
            continue
        before, at = [], 0
        while (
            at < len(runs)
            and isinstance(runs[at][0], int)
            and isinstance(runs[at][1], int)
        ):
            before.extend([runs[at][0]] * runs[at][1])
            at += 1
        if before in ([2, 0, 2], [0, 0, 0, 2], [1, 2, 2]):
            target, target_c = "".join(map(str, before)), 0
        elif (
            len(before) >= 3
            and before[0] == 1
            and before[-1] == 2
            and all(d == 3 for d in before[1:-1])
        ):
            target, target_c = "H", len(before) - 2
        else:
            continue
        if at >= len(runs) or runs[at][0] != 0:
            continue
        loss, suffix = n - runs[at][1], runs[at + 1 :]
        if (
            not isinstance(loss, int)
            or loss < 0
            or len(suffix) != 2
            or suffix[0] != ("W", 1)
        ):
            continue
        if suffix[1][0] == 2 and isinstance(suffix[1][1], int) and suffix[1][1] > 0:
            return target, target_c, loss, suffix[1][1]
    raise RuntimeError("middle-marker symbolic derivation did not finish")
