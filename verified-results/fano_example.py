"""Check the five-gate example for the plane of order two in L-meta-2130."""
from itertools import product

def incident(p, l):
    return (p - l) % 7 in (0, 1, 3)

gates = [('or',0,1), ('or',14,3), ('and',2,8), ('or',15,16), ('and',7,17)]
def run(bits, prune=False):
    wires = list(bits)
    degrees = [0]*7 + [1]*7
    for op, a, b in gates:
        if op == 'and':
            wires.append(wires[a] and wires[b] and not (prune and degrees[a] and degrees[b]))
            degrees.append(degrees[a] + degrees[b])
        else:
            wires.append(wires[a] or wires[b])
            degrees.append(max(degrees[a], degrees[b]))
    return wires

assert all(sum(incident(p,l) for p in range(7)) == 3 for l in range(7))
assert all(sum(incident(p,l) and incident(r,l) for l in range(7)) == 1
           for p in range(7) for r in range(p))
for bits in product([False,True], repeat=14):
    if sum(bits[7:]) <= 2 and run(bits)[-1]:
        assert any(bits[p] and bits[7+l] and incident(p,l) for p in range(7) for l in range(7))
lost, active = [], set()
for l in range(7):
    for p in range(7):
        bits = [i in (p, 7+l) for i in range(14)]
        wires = run(bits)
        if incident(p,l) and wires[-1] and not run(bits, True)[-1]:
            lost.append((p,l))
            active.update(j for j, value in enumerate(wires[14:]) if value)
assert lost == [(0,0),(1,0),(3,0)] and active == {0,1,3,4}
print("Lost pairs:", lost, "active gate indices:", sorted(active))