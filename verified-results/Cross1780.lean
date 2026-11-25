import Mathlib.Data.Finset.Card

namespace VerifiedResults.Cross1780

-- After deleting the false positives, any two points have at most one
-- common incident line. Thus all other lines miss at least one of them.
theorem missing_entries {P L : Type*} [DecidableEq L] (I : P → L → Prop)
    [DecidableRel I] (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (p r : P) (distinct : p ≠ r) (lines : Finset L) :
    lines.card ≤ (lines.filter (fun l => ¬(I p l ∧ I r l))).card + 1 := by
  classical
  obtain ⟨k, _, only⟩ := unique p r distinct
  have sub : lines ⊆ insert k (lines.filter (fun l => ¬(I p l ∧ I r l))) := by
    intro l hl
    by_cases h : I p l ∧ I r l
    · exact Finset.mem_insert.mpr (Or.inl (only l h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hl, h⟩))
  exact (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)

end VerifiedResults.Cross1780
