"""Check least binary monotone circuits for nonempty bipartite C4-free
graphs on 2..4 vertices. A least circuit for any of these nonconstant edge
functions outputs its last gate: a later gate could be deleted.

Truth-table-equivalent wires cannot occur in a least circuit: replace every
later use by the earlier wire and delete the duplicate gate. Commutativity
therefore lets us choose unordered pairs of distinct operands.
"""

from itertools import combinations, product


def check(n):
    edges = list(combinations(range(n), 2))
    inputs = [sum(1 << row for row in range(1 << n) if row >> i & 1) for i in range(n)]
    targets = {}
    for selected in range(1, 1 << len(edges)):
        graph = [e for k, e in enumerate(edges) if selected >> k & 1]
        if not any(all(s[u] != s[v] for u, v in graph) for s in product(range(2), repeat=n)):
            continue
        neighbors = [{v for v in range(n) if tuple(sorted((u, v))) in graph} for u in range(n)]
        if any(len(a & b) > 1 for a, b in combinations(neighbors, 2)):
            continue
        target = 0
        for u, v in graph:
            target |= inputs[u] & inputs[v]
        targets[target] = None

    def search(wires, and_values, remaining, size):
        for a, b in combinations(wires, 2):
            for is_and, value in ((True, a & b), (False, a | b)):
                if value in wires:
                    continue
                ands = and_values + ([value] if is_and else [])
                if remaining > 1:
                    search(wires + [value], ands, remaining - 1, size)
                elif value in targets and targets[value] in (None, size):
                    targets[value] = size
                    # A dirty AND is true on some assignment where the output is false.
                    assert all(g & ~value == 0 for g in ands)

    for size in range(1, 6):
        search(inputs, [], size, size)
        if None not in targets.values():
            break
    assert None not in targets.values()
    print(n, "vertices:", len(targets), "graphs; maximum least size", max(targets.values()))


if __name__ == "__main__":
    for vertices in (2, 3, 4):
        check(vertices)
