"""Exact-size AND/OR/NOT synthesis for the six-input step and its restrictions.

Usage: python search12391.py PATH_TO_CADICAL
Why the four-input search gives a six-input lower bound:
Fix input 4 to one, then input 5 to zero. At each step the fixed input is
essential before restriction and the restricted function is nonconstant.
In a normalized circuit an essential input feeds at least one gate (these
functions are not bare input wires). With that input fixed, every direct
AND/OR reader becomes either a constant or an alias; a NOT reader becomes
a constant. Rewire its readers and propagate constants in topological order.
This removes at least one gate per step and adds none. Empty, unary, or
forward/out-of-range reads in the project model normalize the same way:
missing wires read false, unary AND/OR are aliases, and NOT uses only its
first operand. A nonconstant output needs no constant output gate.

The four-input restriction is true exactly at weights 3 and 4. It depends
on all four inputs, so a circuit needs at least three binary gates: the
connected output cone with k gates has at least k+4-1 edges and at most
2k. We test all smaller candidates from size three onward until SAT.
The two savings and the checked four-input lower bound of seven imply
a six-input lower bound of nine. The explicit monotone circuit attains it.
"""

from itertools import combinations
from pathlib import Path
import subprocess
import sys
import tempfile


def verify_rup(clauses, path):
    """Check every addition against the explicit LRAT hints; require the empty clause."""
    db = {i: c for i, c in enumerate(clauses, 1)}
    with path.open(encoding="ascii") as proof:
        for line in proof:
            fields = line.split()
            if fields[1] == "d":
                # Keeping sound earlier clauses in the database is harmless.
                continue
            words = list(map(int, fields))
            end = words.index(0, 1)
            idx, c, hints = words[0], words[1:end], words[end+1:-1]
            assert words[-1] == 0 and idx not in db and all(h > 0 for h in hints)
            true = {-lit for lit in c}
            contradicted = any(-lit in true for lit in true)
            for hint in hints:
                if contradicted:
                    break
                clause = db[hint]
                assert not any(lit in true for lit in clause)
                left = {lit for lit in clause if -lit not in true}
                if not left:
                    contradicted = True
                else:
                    assert len(left) == 1
                    true.update(left)
            assert contradicted
            if not c:
                return
            db[idx] = c
    raise AssertionError("proof ended without deriving the empty clause")


def solve(solver, n, size, target):
    clauses = []
    next_var = 0

    def fresh():
        nonlocal next_var
        next_var += 1
        return next_var

    rows = 1 << n
    wires = [[fresh() for _ in range(rows)] for _ in range(n + size)]
    for i in range(n):
        for r, var in enumerate(wires[i]):
            clauses.append([var if (r >> i) & 1 else -var])
    readers = [[] for _ in wires]
    gates = []
    for j in range(n, n + size):
        options = [("not", a, a) for a in range(j)]
        options.extend((op, a, b) for a, b in combinations(range(j), 2)
                       for op in ("and", "or"))
        selectors = [fresh() for _ in options]
        clauses.append(selectors)
        clauses.extend([-x, -y] for x, y in combinations(selectors, 2))
        gates.append(list(zip(selectors, options)))
        for selector, (op, a, b) in gates[-1]:
            readers[a].append(selector)
            if a != b:
                readers[b].append(selector)
            for x, y, z in zip(wires[a], wires[b], wires[j]):
                if op == "not":
                    cs = [[-x, -z], [x, z]]
                elif op == "and":
                    cs = [[-z, x], [-z, y], [-x, -y, z]]
                else:
                    cs = [[-x, z], [-y, z], [x, y, -z]]
                clauses.extend([-selector] + c for c in cs)
    # All inputs are essential for these targets. A least circuit has every
    # gate in the output cone. Constants and redundant binary reads simplify.
    clauses.extend(readers[:-1])
    clauses.extend([z if (target >> r) & 1 else -z] for r, z in enumerate(wires[-1]))
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / "search.cnf"
        with path.open("w", encoding="ascii") as out:
            out.write(f"p cnf {next_var} {len(clauses)}\n")
            for c in clauses:
                out.write(" ".join(map(str, c)) + " 0\n")
        proof = Path(temp) / "proof.lrat"
        result = subprocess.run([solver, "-q", "--plain", "--lrat", "--no-binary",
                                 str(path), str(proof)], capture_output=True, text=True)
        if result.returncode == 20 and "s UNSATISFIABLE" in result.stdout:
            verify_rup(clauses, proof)
            return None
    if result.returncode != 10 or "s SATISFIABLE" not in result.stdout:
        raise RuntimeError(result.stdout[-500:] + result.stderr[-500:])
    model = {int(s) for line in result.stdout.splitlines() if line.startswith("v ")
             for s in line.split()[1:]}
    circuit = [next(op for sel, op in opts if sel in model) for opts in gates]
    for r in range(rows):
        vals = [bool(r & (1 << i)) for i in range(n)]
        for op, a, b in circuit:
            vals.append(not vals[a] if op == "not" else
                        vals[a] and vals[b] if op == "and" else vals[a] or vals[b])
        assert vals[-1] == bool(target & (1 << r))
    return circuit


if __name__ == "__main__":
    full = (3907577984 << 32) + 3900762240
    assert any(((full >> r) ^ (full >> (r | 16))) & 1 for r in range(64))
    assert any(((full >> (r | 16)) ^ (full >> (r | 16 | 32))) & 1 for r in range(64))
    restricted = sum(((full >> (r + 16)) & 1) << r for r in range(16))
    assert restricted == sum(1 << r for r in range(16) if r.bit_count() >= 3)
    for r in range(64):
        a, b, c, d, e, f = (bool(r & (1 << i)) for i in range(6))
        w = d or (e and f)
        nine = ((a and b) and (c or w)) or ((a or b) and (c and w))
        assert nine == bool(full & (1 << r))
    for size in range(3, 8):
        witness = solve(sys.argv[1], 4, size, restricted)
        print(f"four inputs, {size} gates: {witness if witness else 'UNSAT'}", flush=True)
        if witness:
            break
