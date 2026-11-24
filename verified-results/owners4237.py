"""Finite edge-ownership experiment for L-meta-4237. Run with Python 3."""

from itertools import combinations, combinations_with_replacement


def incidence_graph(q):
    # Normalized projective points and, dually, line coefficient vectors over F_q.
    vectors = ([(1, a, b) for a in range(q) for b in range(q)]
               + [(0, 1, a) for a in range(q)] + [(0, 0, 1)])
    half = len(vectors)
    neighbors = []
    for point in vectors:
        neighbors.append({j for j, line in enumerate(vectors)
                          if sum(x * y for x, y in zip(point, line)) % q == 0})
    assert all(len(row) == q + 1 for row in neighbors)
    assert all(sum(j in row for row in neighbors) == q + 1 for j in range(half))
    # Bipartiteness rules out triangles. A 4-cycle would give two common lines.
    assert all(len(a & b) == 1 for a, b in combinations(neighbors, 2))
    return 2 * half, {(i, half + j) for i, row in enumerate(neighbors) for j in row}


def edge_circuit(n, edges, pad):
    gates = []

    def gate(op, a, b):
        gates.append((op, a, b))
        return n + len(gates) - 1

    inputs = [gate("and", i, i) if pad else i for i in range(n)]
    terms = [gate("and", inputs[u], inputs[v]) for u, v in sorted(edges)]
    output = terms[0]
    for term in terms[1:]:
        output = gate("or", output, term)
    return gates, output


def evaluate(inputs, gates, output, edge_rows):
    # One bit per input assignment. The second list tracks which rows made
    # any AND in a wire's cone (including that wire itself) true.
    values = list(inputs)
    true_in_cone = [0] * len(inputs)
    clean_owned = 0
    for op, a, b in gates:
        descendants = true_in_cone[a] | true_in_cone[b]
        if op == "and":
            value = values[a] & values[b]
            if value & ~edge_rows == 0:
                clean_owned |= value & ~descendants
            true_in_cone.append(descendants | value)
        else:
            value = values[a] | values[b]
            true_in_cone.append(descendants)
        values.append(value)
    return values[output], clean_owned


def check(q):
    n, edges = incidence_graph(q)
    inputs = [0] * n
    edge_rows = 0
    for row, pair in enumerate(combinations_with_replacement(range(n), 2)):
        u, v = pair
        flag = 1 << row
        inputs[u] |= flag
        inputs[v] |= flag
        if pair in edges:
            edge_rows |= flag

    for pad in (False, True):
        gates, output = edge_circuit(n, edges, pad)
        value, owned = evaluate(inputs, gates, output, edge_rows)
        assert value == edge_rows
        assert owned == (0 if pad else edge_rows)
        assert len(gates) == 2 * len(edges) - 1 + (n if pad else 0)
        if q == 2:
            # Independent truth table for all 16,384 assignments.
            all_inputs = [0] * n
            expected = 0
            for mask in range(1 << n):
                flag = 1 << mask
                for v in range(n):
                    if mask & (1 << v):
                        all_inputs[v] |= flag
                if any(mask & (1 << u) and mask & (1 << v) for u, v in edges):
                    expected |= flag
            assert evaluate(all_inputs, gates, output, expected)[0] == expected
    print(f"q={q}: {n} vertices, degree {q + 1}, {len(edges)} edges; "
          f"clean-owned edges {len(edges)} before padding, 0 after")


if __name__ == "__main__":
    for prime in (2, 3, 5, 7):
        check(prime)
