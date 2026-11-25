import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Polynomial

namespace VerifiedResults.CubicRoots

noncomputable def positive (p : Polynomial ℝ) := p.roots.toFinset.filter (0 < ·)

private theorem signs (f : Polynomial ℝ) (nz : f ≠ 0) : f.signVariations < f.support.card := by
  by_cases e : f.eraseLead = 0
  · have m := f.eraseLead_add_monomial_natDegree_leadingCoeff
    rw [e, zero_add] at m
    rw [← m, signVariations_monomial]
    rw [m, ← f.card_support_eraseLead_add_one nz]
    omega
  · have h := signs f.eraseLead e
    have up := f.signVariations_le_eraseLead_succ
    have count := f.card_support_eraseLead_add_one nz
    omega
termination_by f.support.card
decreasing_by exact f.eraseLead_support_card_lt nz

theorem sparse_bound (p : Polynomial ℝ) : (positive p).card ≤ p.support.card - 1 := by
  classical
  by_cases z : p = 0
  · simp [positive,z]
  have h := signs p z
  have d := p.roots_countP_pos_le_signVariations
  rw [Multiset.countP_eq_card_filter] at d
  unfold positive
  rw [← Multiset.toFinset_filter]
  have le := Multiset.toFinset_card_le (p.roots.filter (0 < ·))
  omega

-- If the third summand vanishes, signs can be absorbed into a and b
-- because the powers are odd.
theorem two_cubes (a b : Polynomial ℝ) (ha : a.support.card ≤ 4) (hb : b.support.card ≤ 4) :
    (positive (a^3 + b^3)).card ≤ 7 := by
  classical
  by_cases z : a+b = 0
  · have e : b = -a := by exact eq_neg_of_add_eq_zero_left (add_comm a b ▸ z)
    have zero : a^3+b^3 = 0 := by rw [e]; ring
    simp [positive,zero]
  have sub : positive (a^3+b^3) ⊆ positive (a+b) := by
    intro x hx
    obtain ⟨root,pos⟩ := Finset.mem_filter.mp hx
    have e := (Multiset.mem_toFinset.mp root)
    have val := (Polynomial.isRoot_of_mem_roots e)
    change Polynomial.eval x _ = 0 at val
    simp only [eval_add, eval_pow] at val
    apply Finset.mem_filter.mpr
    refine ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots z).mpr ?_),pos⟩
    change Polynomial.eval x (a+b) = 0
    rw [eval_add]
    have cub : (a.eval x)^3 = (-(b.eval x))^3 := by linarith
    have eq := (Odd.strictMono_pow (by decide : Odd 3)).injective cub
    linarith
  have supp := Finset.card_le_card (Polynomial.support_add (p := a) (q := b))
  have union := Finset.card_union_le a.support b.support
  have h := (Finset.card_le_card sub).trans (sparse_bound (a+b))
  omega

private theorem product_bound (a b : Polynomial ℝ) :
    (positive (a*b)).card ≤ (positive a).card + (positive b).card := by
  classical
  by_cases zero : a*b = 0
  · simp [zero, positive]
  have sub : positive (a*b) ⊆ positive a ∪ positive b := by
    intro x hx
    obtain ⟨hm,hx⟩ := Finset.mem_filter.mp hx
    rw [Polynomial.roots_mul zero, Multiset.toFinset_add] at hm
    rcases Finset.mem_union.mp hm with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h,hx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h,hx⟩)
  exact (Finset.card_le_card sub).trans (Finset.card_union_le ..)

theorem zero_sum_three_cubes (a b c : Polynomial ℝ) (h : a+b+c = 0)
    (ha : a.support.card ≤ 4) (hb : b.support.card ≤ 4) (hc : c.support.card ≤ 4) :
    (positive (a^3+b^3+c^3)).card ≤ 9 := by
  have e : c = -(a+b) := eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h)
  have three : C (3 : ℝ) = (3 : Polynomial ℝ) := map_ofNat _ _
  have id : a^3+b^3+c^3 = C (3 : ℝ) * (a*b*c) := by rw [e, three]; ring
  rw [id]
  have h0 : (positive (C (3 : ℝ))).card = 0 := by simp [positive]
  have h1 := product_bound (C (3 : ℝ)) (a*b*c)
  have h2 := product_bound (a*b) c
  have h3 := product_bound a b
  have ba := sparse_bound a
  have bb := sparse_bound b
  have bc := sparse_bound c
  omega

end VerifiedResults.CubicRoots
