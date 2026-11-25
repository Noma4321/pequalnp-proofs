import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace VerifiedResults.StarBudget

-- Each nonempty star contributes one AND and (degree - 1) binary ORs.
-- Combining all stars takes one fewer OR than the number of stars.
theorem star_budget {ι : Type*} (stars : Finset ι) (degree : ι → ℕ)
    (N q : ℕ) (pos : ∀ i ∈ stars, 0 < degree i)
    (cap : ∀ i ∈ stars, degree i ≤ q + 1)
    (cover : N * (q + 1) ≤ ∑ i ∈ stars, degree i) :
    N * (q + 1) + N - 1 ≤
      (∑ i ∈ stars, (degree i - 1 + 1)) + stars.card - 1 := by
  have upper : (∑ i ∈ stars, degree i) ≤ stars.card * (q + 1) := by
    simpa using (Finset.sum_le_sum cap)
  have count : N ≤ stars.card := by
    by_contra! h
    have smaller := Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos q)
    exact (not_lt_of_ge (cover.trans upper)) smaller
  have eq : (∑ i ∈ stars, (degree i - 1 + 1)) = ∑ i ∈ stars, degree i := by
    apply Finset.sum_congr rfl
    intro i hi
    have := pos i hi
    omega
  omega

end VerifiedResults.StarBudget
