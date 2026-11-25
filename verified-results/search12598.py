"""Check whether negation can improve on a nine-gate monotone circuit.

Run with Python 3. No solver, external data, or third-party packages are used.
The target uses the six input bits in little-endian order.
"""

from functools import lru_cache
from itertools import combinations


TARGET = (4008373994 << 32) + 4008372360
MASK = (1 << 64) - 1
INPUTS = tuple(sum(1 << r for r in range(64) if r & (1 << i)) for i in range(6))


def witness(a, b, c, d, e, f):
    g = e | f
    u = c | d
    v = c & d
    h = b & u
    p = a | h
    q = v | g
    k = p & q
    m = a & b
    return k | m


def normalized(wire):
    # With free NOT gates a wire and its complement are interchangeable.
    return wire ^ MASK if wire & 1 else wire


def check(target, budget):
    goal = normalized(target)
    pairs = [(i, j) for i in range(64) if target >> i & 1
             for j in range(64) if not (target >> j & 1)]
    required = (1 << len(pairs)) - 1

    @lru_cache(maxsize=8192)
    def distinguishes(wire):
        return sum(1 << k for k, (i, j) in enumerate(pairs)
                   if ((wire >> i) ^ (wire >> j)) & 1)

    def separated(wires):
        covered = 0
        for wire in wires:
            covered |= distinguishes(wire)
        return covered == required

    @lru_cache(maxsize=65536)
    def reachable(wires, remaining):
        if goal in wires:
            return True
        if not remaining or len(wires) > remaining + 1 or not separated(wires):
            return False
        for i, j in combinations(range(len(wires)), 2):
            a, b = wires[i], wires[j]
            rest = tuple(x for k, x in enumerate(wires) if k != i and k != j)
            for z in {normalized(x & y) for x in (a, a ^ MASK) for y in (b, b ^ MASK)}:
                if z == 0 or z in wires:
                    continue
                for kept in ((), (a,), (b,), (a, b)):
                    if len(rest) + len(kept) + 1 > remaining:
                        continue
                    after = tuple(sorted((*rest, *kept, z)))
                    if reachable(after, remaining - 1):
                        return True
        return False

    # Use the connected output cone of a least circuit and discard each
    # operand just after its final use. Essential inputs all start live.
    # Its next binary gate consumes two distinct wires and retains whichever
    # operands are used again. With k gates left at most k+1 wires can
    # still be live: each gate reduces the live count by at most one.
    # If two rows now agree on all live wires, no later gate separates them.
    # Useless gates, constants, aliases and duplicate/complementary wires
    # simplify out. Project reads outside the current wire list are false.
    # These observations make the recursion exhaustive for a least circuit
    # over AND/OR with free inversions, including inversions on the output.
    assert all(any(((target >> r) ^ (target >> (r ^ (1 << i)))) & 1
                   for r in range(64)) for i in range(6))
    return reachable(tuple(sorted(INPUTS)), budget)


if __name__ == "__main__":
    if witness(*INPUTS) != TARGET:
        raise AssertionError("the monotone circuit disagrees with the table")
    if check(1 << 63, 4) or not check(1 << 63, 5):
        raise AssertionError("six-input AND should need exactly five binary gates")
    if check(TARGET, 8) or not check(TARGET, 9):
        raise AssertionError("the exhaustive search disagrees with the nine-gate minimum")
    print("Checked 64 rows of the nine-gate monotone witness.")
    print("Exhausted up to eight binary gates even with free negations.")
    print("Minimum size is nine in both the general and monotone models.")
