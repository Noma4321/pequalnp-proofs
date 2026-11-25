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


def synthesis_path(target, budget, *, monotone=False):
    """Return successive (operand table, operand table, result table) triples."""
    goal = target if monotone else normalized(target)
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
            return ()
        if not remaining or len(wires) > remaining + 1 or not separated(wires):
            return None
        for i, j in combinations(range(len(wires)), 2):
            a, b = wires[i], wires[j]
            rest = tuple(x for k, x in enumerate(wires) if k != i and k != j)
            choices = ((a & b, a | b) if monotone else
                       {normalized(x & y) for x in (a, a ^ MASK) for y in (b, b ^ MASK)})
            for z in choices:
                if z == 0 or z in wires:
                    continue
                for kept in ((), (a,), (b,), (a, b)):
                    if len(rest) + len(kept) + 1 > remaining:
                        continue
                    after = tuple(sorted((*rest, *kept, z)))
                    tail = reachable(after, remaining - 1)
                    if tail is not None:
                        return ((a, b, z), *tail)
        return None

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


def check(target, budget):
    return synthesis_path(target, budget) is not None


def monotone_witness(target, budget):
    """Convert a synthesized path to ordinary numbered gates and replay every row."""
    path = synthesis_path(target, budget, monotone=True)
    if path is None:
        return None
    indices = {table: i for i, table in enumerate(INPUTS)}
    gates = []
    for a, b, z in path:
        op = "and" if z == a & b else "or"
        gates.append((op, indices[a], indices[b]))
        indices[z] = 6 + len(gates) - 1
    for row in range(64):
        values = [bool(row & (1 << i)) for i in range(6)]
        for op, i, j in gates:
            values.append((values[i] and values[j]) if op == "and" else (values[i] or values[j]))
        if values[indices[target]] != bool(target & (1 << row)):
            raise AssertionError("synthesized circuit failed replay")
    return gates


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
