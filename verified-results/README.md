# Verified partial results

These files record work on three P vs NP proof-desk assignments. The Lean files were checked locally with the repository's pinned Lean 4.36.0 toolchain. The Python scripts reproduce finite experiments. Upstream review and credit are tracked separately by the project.

| Assignment | Result | Evidence |
| --- | --- | --- |
| L-meta-2130 | The requested gate bound holds for all plane orders through 43. At any order it also holds if at most 1,893 points or at most 1,893 lines participate, or if every participating point and line has degree at most 44. Larger dense cases remain open. | [Lean proofs](Sensitivity2130.lean) |
| L-meta-2130 | In the five-gate order-two example, pruning loses three pairs and four gates are active. Soundness was tested on all 16,384 inputs. | [Finite example](fano_example.py) |
| L-meta-1985 | Evaluating monotone circuits on packed bit vectors agrees at each bit with evaluating the same assignment separately. The Heawood edge function has 21 minimal true assignments and 37 maximal false assignments. The 27-gate lower bound remains open in this work. | [Lean evaluation lemma](Packed1985.lean) and [row enumeration](boundary_rows.py) |
| L-meta-2775 | Factoring two AND leaves that share an input preserves the OR of the leaves. Given the binary-tree gate count, the rebuilt expression saves one gate. Circuit rewiring passed 216 minimal-shape test cases and 5,000 seeded cases, exhaustively over the inputs of each case. A general Lean proof of rewiring remains open. | [Lean lemmas](Factor2775.lean) and [circuit tests](Factor2775.py) |

[Wire renumbering for L-meta-2775](Compress2775.lean) proves that deleting marked gates and renumbering the retained wires preserves every retained value, provided each retained gate reads only retained earlier wires. The construction keeps exactly the marked-for-retention gates and preserves binary AND/OR operations with backward reads. The theorem `isolated_closed` derives the retention condition from the backward-read and isolation hypotheses when removing the OR tree and both shared-input AND gates. The replacement OR chain uses one binary gate per remaining leaf, reads earlier wires, and returns the disjunction of the starting wire and those leaves. [Original-tree semantics](Original2775.lean) proves that the circuit output equals the disjunction of the factored term and the remaining leaves, evaluated on the original wires. The proof uses tree propagation and wire evaluation from L_meta_536. The theorem `rebuild_inputs` proves every operand of the two factored gates and every remaining leaf names a real, retained wire. The complete smaller-circuit construction still needs to link their renumbered values to the replacement gates and establish its final size.

To reproduce the checks after setting up the project's dependencies, run these commands in the checkout's lean directory.

```sh
lake build PEqualNP.Defs
lake env lean ../verified-results/Sensitivity2130.lean
lake env lean ../verified-results/Packed1985.lean
lake env lean ../verified-results/Factor2775.lean
lake env lean ../verified-results/Compress2775.lean
lake env lean ../verified-results/Original2775.lean
python ../verified-results/fano_example.py
python ../verified-results/boundary_rows.py
python ../verified-results/Factor2775.py
```