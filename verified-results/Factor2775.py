"""Test the proposed output-tree rewrite on finite AO2 circuits for L-meta-2775."""
from collections import Counter
from itertools import combinations, product, permutations
from random import Random

def masks(n):
    return [sum(1 << row for row in range(1 << n) if row >> i & 1) for i in range(n)]

def evaluate(n, gates, output):
    wires = masks(n)
    for op, u, v in gates:
        assert op in ('and', 'or') and 0 <= u < len(wires) and 0 <= v < len(wires)
        wires.append(wires[u] & wires[v] if op == 'and' else wires[u] | wires[v])
    return wires[output]

def rewrite(n, gates, output, tree, leaves, first, second, a, b, c):
    """Keep the non-tree prefix in topological order; rebuild the entire OR tree."""
    assert gates[first] in [('and', a, b), ('and', b, a)]
    assert gates[second] in [('and', a, c), ('and', c, a)]
    assert first != second and {n+first, n+second} <= leaves
    internal = {n+j for j in tree}
    assert output in internal and internal.isdisjoint(leaves)
    usage = Counter()
    for j in tree:
        op, u, v = gates[j]
        assert op == 'or' and {u,v} <= leaves | internal and max(u,v) < n+j
        usage.update((u,v))
    assert all(usage[x] == int(x != output) for x in leaves | internal)
    assert len(tree)+1 == len(leaves)
    new, rename = [], {i:i for i in range(n)}
    def append(op, u, v):
        new.append((op, u, v))
        return n+len(new)-1
    for j, (op,u,v) in enumerate(gates):
        if j not in tree:
            assert not {u,v} & (internal | {n+first,n+second})
        if j not in tree and j not in (first,second):
            rename[n+j] = append(op,rename[u],rename[v])
    fused = append('and',rename[a],append('or',rename[b],rename[c]))
    for leaf in sorted(leaves - {n+first,n+second}):
        fused = append('or',fused,rename[leaf])
    assert len(new)+1 == len(gates)
    return new,fused

def check(n,gates,out,tree,leaves,indices,abc):
    new,output=rewrite(n,gates,out,tree,leaves,*indices,*abc)
    assert evaluate(n,gates,out)==evaluate(n,new,output)

def run():
    base=0
    for a,b,c in product(range(3),repeat=3):
        for ab in permutations((a,b)):
            for ac in permutations((a,c)):
                for root in permutations((3,4)):
                    check(3,[('and',*ab),('and',*ac),('or',*root)],5,{2},{3,4},(0,1),(a,b,c))
                    base+=1
    rng=Random(2775)
    for _ in range(5000):
        n=rng.randint(2,7)
        gates=[]
        def emit(op,u,v):
            gates.append((op,u,v))
            return n+len(gates)-1
        pool=list(range(n))
        def ordinary():
            pool.append(emit(rng.choice(('and','or')),rng.choice(pool),rng.choice(pool)))
        for j in range(rng.randrange(10)):
            ordinary()
        a,b=rng.choice(pool),rng.choice(pool)
        first=emit('and',a,b)
        for j in range(rng.randrange(5)):
            ordinary()
        c=rng.choice(pool)
        second=emit('and',c,a)
        leaves={first,second,*rng.sample(pool,rng.randrange(min(len(pool),8)+1))}
        current=sorted(leaves)
        tree=set()
        while len(current)>1:
            if rng.randrange(2): ordinary()
            u=current.pop(rng.randrange(len(current)))
            v=current.pop(rng.randrange(len(current)))
            w=emit('or',u,v)
            tree.add(w-n)
            current.append(w)
        for j in range(rng.randrange(3)): ordinary()
        check(n,gates,current[0],tree,leaves,(first-n,second-n),(a,b,c))
    print(f'{base} minimal-shape cases and 5000 seeded circuits passed every input assignment.')
if __name__=='__main__':
    run()
