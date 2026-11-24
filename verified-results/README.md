# Verified partial results

These files record work on three P vs NP proof-desk assignments. The Lean files were checked locally with the repository's pinned Lean 4.36.0 toolchain. The Python scripts reproduce finite experiments. Upstream review and credit are tracked separately by the project.

| Assignment | Result | Evidence |
| --- | --- | --- |
| L-meta-2130 | The requested gate bound holds for all plane orders through 43. At any order it also holds if at most 1,893 points or at most 1,893 lines participate, or if every participating point and line has degree at most 44. Larger dense cases remain open. | [Lean proofs](Sensitivity2130.lean) |
| L-meta-2130 | In the five-gate order-two example, pruning loses three pairs and four gates are active. Soundness was tested on all 16,384 inputs. | [Finite example](fano_example.py) |
| L-meta-1985 | Evaluating monotone circuits on packed bit vectors agrees at each bit with evaluating the same assignment separately. The Heawood edge function has 21 minimal true assignments and 37 maximal false assignments. The 27-gate lower bound remains open in this work. | [Lean evaluation lemma](Packed1985.lean) and [row enumeration](boundary_rows.py) |
| L-meta-2775 | Factoring two AND leaves that share an input preserves the OR of the leaves. Given the binary-tree gate count, the rebuilt expression saves one gate. Circuit rewiring passed 216 minimal-shape test cases and 5,000 seeded cases, exhaustively over the inputs of each case. A general Lean proof of rewiring remains open. | [Lean lemmas](Factor2775.lean) and [circuit tests](Factor2775.py) |

To reproduce the checks after setting up the project's dependencies, run these commands in the checkout's lean directory.

```sh
lake build PEqualNP.Defs
lake env lean ../verified-results/Sensitivity2130.lean
lake env lean ../verified-results/Packed1985.lean
lake env lean ../verified-results/Factor2775.lean
python ../verified-results/fano_example.py
python ../verified-results/boundary_rows.py
python ../verified-results/Factor2775.py
```