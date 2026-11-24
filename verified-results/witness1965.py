"""Verify a 29-gate near witness for L-meta-1965 on all 14-bit inputs."""

from itertools import product


def check():
    gates = []

    def gate(op, left, right):
        wire = 14 + len(gates)
        assert 0 <= left < wire and 0 <= right < wire and left != right
        gates.append((op, left, right))
        return wire

    stars = []
    for point in range(7):
        neighbors = [7 + (point - offset) % 7 for offset in (0, 1, 3)]
        line_or = gate("or", gate("or", neighbors[0], neighbors[1]), neighbors[2])
        star = gate("and", point, line_or)
        if point == 0:
            extended = gate("or", star, 1)
            special = gate("and", star, extended)
            star = special
        stars.append(star)
    output = stars[0]
    for star in stars[1:]:
        output = gate("or", output, star)
    assert len(gates) == 29
    cone = {output}
    for j in reversed(range(len(gates))):
        if 14 + j in cone:
            cone.update(gates[j][1:])
    assert special in cone and gates[special - 14][0] == "and"
    edges = [(p, 7 + l) for p, l in product(range(7), repeat=2)
             if p in (l, (l + 1) % 7, (l + 3) % 7)]
    assert len(edges) == 21
    for mask in range(1 << 14):
        wires = [bool(mask & (1 << i)) for i in range(14)]
        for op, a, b in gates:
            wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
        assert wires[output] == any(wires[p] and wires[l] for p, l in edges)
        if mask in (1, 1 << 7):
            assert all(not wires[w] for w in gates[special - 14][1:])
        if mask == 1 + (1 << 7):
            assert wires[special]
    print("29 gates; all 16384 assignments and the distinguished AND checked")


if __name__ == "__main__":
    check()
