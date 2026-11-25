import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Sym.Card

open Polynomial

namespace VerifiedResults.Binomial252

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

private theorem exponent_split {a b : Polynomial ℝ} {k : ℕ} (h : k ∈ (a*b).support) :
    ∃ i ∈ a.support, ∃ j ∈ b.support, i+j=k := by
  have hn := Polynomial.mem_support_iff.mp h
  rw [coeff_mul] at hn
  obtain ⟨p,mp,nonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact ⟨p.1, Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul nonzero),
    p.2, Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul nonzero),
    Finset.mem_antidiagonal.mp mp⟩

private theorem pair_cover (S : Finset ℕ) (h : S.card ≤ 2) :
    ∃ a b : ℕ, ∀ k ∈ S, k = a ∨ k = b := by
  by_cases eq : S.card = 2
  · obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp eq
    exact ⟨a,b,by simp⟩
  · obtain ⟨a,ha⟩ := Finset.card_le_one_iff_subset_singleton.mp (show S.card ≤ 1 by omega)
    exact ⟨a,a,fun k hk => Or.inl (Finset.mem_singleton.mp (ha hk))⟩

private theorem one_cube (g : Polynomial ℝ) (small : g.support.card ≤ 2) :
    (g^3).support.card ≤ 4 := by
  classical
  obtain ⟨a,b,h⟩ := pair_cover g.support small
  let E : Finset ℕ := {a+a+a, a+a+b, a+b+b, b+b+b}
  have inc : (g^3).support ⊆ E := by
    intro k hk
    rw [pow_succ, pow_two] at hk
    obtain ⟨t,ht,r,hr,rfl⟩ := exponent_split hk
    obtain ⟨p,hp,q,hq,rfl⟩ := exponent_split ht
    rcases h p hp with rfl | rfl <;> rcases h q hq with rfl | rfl <;>
      rcases h r hr with rfl | rfl <;> simp [E, add_comm, add_left_comm]
  exact (Finset.card_le_card inc).trans Finset.card_le_four

noncomputable def total (s : Fin 5 → ℝ) (g : Fin 5 → Polynomial ℝ) :=
  ∑ i, C (s i) * g i ^ 3

theorem support_bound (s : Fin 5 → ℝ) (g : Fin 5 → Polynomial ℝ)
    (small : ∀ i, (g i).support.card ≤ 2) : (total s g).support.card ≤ 20 := by
  classical
  let U := Finset.univ.biUnion fun i => (g i ^ 3).support
  have inc : (total s g).support ⊆ U := by
    intro k hk
    have hn := Polynomial.mem_support_iff.mp hk
    unfold total at hn
    rw [finsetSum_coeff] at hn
    obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    rw [coeff_C_mul] at hi
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Polynomial.mem_support_iff.mpr
      (right_ne_zero_of_mul hi)⟩
  calc
    _ ≤ U.card := Finset.card_le_card inc
    _ ≤ ∑ i : Fin 5, (g i ^ 3).support.card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 5, 4 := Finset.sum_le_sum (fun i _ => one_cube _ (small i))
    _ = 20 := by simp

theorem at_most_nineteen (s : Fin 5 → ℝ) (g : Fin 5 → Polynomial ℝ)
    (small : ∀ i, (g i).support.card ≤ 2) : (positive (total s g)).card ≤ 19 := by
  have := support_bound s g small
  have := sparse_bound (total s g)
  omega

theorem shared_root (s : Fin 5 → ℝ) (g : Fin 5 → Polynomial ℝ)
    (small : ∀ i, (g i).support.card ≤ 2)
    (r : ℝ) (pos : 0 < r) (common : ∀ i, (g i).IsRoot r) :
    (positive (total s g)).card ≤ 17 := by
  classical
  by_cases zero : total s g = 0
  · simp [positive,zero]
  have divides : (X - C r)^3 ∣ total s g := by
    apply Finset.dvd_sum
    intro i _
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr (common i)) 3) _
  obtain ⟨q,hq⟩ := divides
  have nz : (X - C r)^3 * q ≠ 0 := hq ▸ zero
  have roots : (total s g).roots = r ::ₘ r ::ₘ r ::ₘ q.roots := by
    rw [hq,roots_mul nz,roots_pow,roots_X_sub_C]
    simp [succ_nsmul, add_assoc, Multiset.singleton_add]
  have budget := (total s g).roots_countP_pos_le_signVariations
  have count := signs _ zero
  have cap := support_bound s g small
  rw [roots, Multiset.countP_eq_card_filter] at budget
  simp [pos] at budget
  have sub : positive (total s g) ⊆ insert r (positive q) := by
    intro x hx
    simp only [positive,Finset.mem_filter,roots,Multiset.mem_toFinset,Multiset.mem_cons] at hx
    rcases hx with ⟨h,hpos⟩
    rcases h with h|h|h|h
    all_goals first | exact Finset.mem_insert.mpr (Or.inl h) |
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr h,hpos⟩))
  have bound := (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
  have aux : (positive q).card ≤ (q.roots.filter (0 < ·)).card := by
    unfold positive
    rw [← Multiset.toFinset_filter]
    exact Multiset.toFinset_card_le _
  omega

end VerifiedResults.Binomial252

