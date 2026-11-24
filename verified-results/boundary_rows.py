"""Enumerate boundary assignments for the Heawood edge function in L-meta-1985."""
neighbors = [(7,8,10), (7,9,13), (8,12,13), (7,11,12), (10,11,13), (9,10,12), (8,9,11)]
positive = [(1 << p) | (1 << l) for p, lines in enumerate(neighbors) for l in lines]

def hit(x):
    return any((x & edge) == edge for edge in positive)

maximal_false = [
    x for x in range(1 << 14) if not hit(x) and
    all(hit(x | (1 << i)) for i in range(14) if not (x >> i) & 1)
]
assert len(set(positive)) == 21 and len(maximal_false) == 37
print("21 minimal true rows and 37 maximal false rows:", maximal_false)