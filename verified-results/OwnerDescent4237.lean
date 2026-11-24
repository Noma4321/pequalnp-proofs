import PEqualNP.Defs.EdgeOwnership

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

namespace VerifiedResults.OwnerDescent

-- Paths point from an active AND in a strict cone toward the gate above it.
def ActiveBelow (n : ℕ) (C : Circuit) (u v : Fin n) (i j : ℕ) : Prop :=
  i < j ∧ InCone n C i j ∧ (gateAt C i).op = GateOp.and ∧
    gateVal n C i (pairInput u v) = true

theorem reachable_owner {n : ℕ} (C : Circuit) (u v : Fin n) (j : ℕ)
    (bound : j < C.gates.length) (op : (gateAt C j).op = GateOp.and)
    (active : gateVal n C j (pairInput u v) = true) :
    ∃ i, Owns n C i u v ∧ Relation.ReflTransGen (ActiveBelow n C u v) i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases below : ∃ i, ActiveBelow n C u v i j
    · obtain ⟨k, step⟩ := below
      obtain ⟨i, owner, path⟩ := ih k step.1 (lt_trans step.1 bound) step.2.2.1 step.2.2.2
      exact ⟨i, owner, path.tail step⟩
    · refine ⟨j, ⟨bound, op, active, ?_⟩, .refl⟩
      intro i earlier cone andGate
      cases value : gateVal n C i (pairInput u v) with
      | false => rfl
      | true => exact (below ⟨i, earlier, cone, andGate, value⟩).elim

end VerifiedResults.OwnerDescent
