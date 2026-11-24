import PEqualNP.Defs.TopForm
import Mathlib.Data.Finset.Card

namespace Factor2775

-- All other OR leaves keep their original values after the rewrite.
theorem factor_leaves (L : Finset ℕ) (i j : ℕ) (hi : i ∈ L) (hj : j ∈ L)
    (v : ℕ → Bool) (a b c : Bool) (h1 : v i = (a && b)) (h2 : v j = (a && c)) :
    (∃ k ∈ L, v k = true) ↔ (a && (b || c)) = true ∨
      ∃ k ∈ (L.erase i).erase j, v k = true := by
  constructor
  · rintro ⟨k, hk, hv⟩
    by_cases ei : k = i
    · subst k
      rw [h1] at hv
      simp_all only [Bool.and_eq_true, Bool.or_eq_true, true_or, or_true, and_self]
    by_cases ej : k = j
    · subst k
      rw [h2] at hv
      simp_all only [Bool.and_eq_true, Bool.or_eq_true, true_or, or_true, and_self]
    exact Or.inr ⟨k, Finset.mem_erase.mpr ⟨ej, Finset.mem_erase.mpr ⟨ei,hk⟩⟩, hv⟩
  · rintro (h | ⟨k, hk, hv⟩)
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      rcases h with ⟨ha, hb | hc⟩
      · exact ⟨i,hi,by simp [h1,ha,hb]⟩
      · exact ⟨j,hj,by simp [h2,ha,hc]⟩
    · exact ⟨k, (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2, hv⟩

theorem factor_size (other tree : ℕ) (L : Finset ℕ) (i j : ℕ) (hi : i ∈ L)
    (hj : j ∈ L) (ne : j ≠ i) (tree_count : L.card = tree + 1) :
    other + 2 + ((L.erase i).erase j).card + 1 = other + 2 + tree := by
  have hj' := Finset.mem_erase.mpr ⟨ne,hj⟩
  have hpos := Finset.card_pos.mpr ⟨j,hj'⟩
  rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]
  rw [Finset.card_erase_of_mem hi] at hpos
  omega

end Factor2775