import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Sym.Card

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

private theorem pencil_chart (a b : Polynomial ℝ) (u v : ℝ)
    (ha : a.support.card ≤ 4) (hb : b.support.card ≤ 4) (lead : 1+u^3 ≠ 0) :
    (positive (a^3+b^3+(C u*a+C v*b)^3)).card ≤ 21 := by
  classical
  let P := a^3+b^3+(C u*a+C v*b)^3
  change (positive P).card ≤ 21
  by_cases dep : ∃ t : ℝ, a = C t*b
  · obtain ⟨t, ht⟩ := dep
    have id : P = C (t^3+1+(u*t+v)^3)*b^3 := by simp [P,ht]; ring
    rw [id]
    have c := product_bound (C (t^3+1+(u*t+v)^3)) (b^3)
    have constant (k : ℝ) : (positive (C k)).card = 0 := by simp [positive]
    have z := constant (t^3+1+(u*t+v)^3)
    have r : positive (b^3) = positive b := by simp [positive, roots_pow]
    rw [r,z] at c
    have s := sparse_bound b
    omega
  let Q : Polynomial ℝ := C (1+u^3)*X^3 + C (3*u^2*v)*X^2 +
    C (3*u*v^2)*X + C (1+v^3)
  have deg : Q.natDegree = 3 := by unfold Q; compute_degree!
  have nz : Q ≠ 0 := by intro h; simp [h] at deg
  let R := Q.roots.toFinset
  let dirs : Finset ℝ := if R.Nonempty then R else {0}
  have nonempty : dirs.Nonempty := by by_cases h : R.Nonempty <;> simp [dirs,h]
  have incl : R ⊆ dirs := by by_cases h : R.Nonempty <;> simp_all [dirs, Finset.not_nonempty_iff_eq_empty]
  have num : dirs.card ≤ 3 := by
    have := (Multiset.toFinset_card_le Q.roots).trans Q.card_roots'
    by_cases h : R.Nonempty <;> simp_all [dirs,R]
  let fiber (t : ℝ) := positive (a-C t*b)
  have small (t : ℝ) : (fiber t).card ≤ 7 := by
    have sub : (a-C t*b).support ⊆ a.support ∪ b.support := by
      intro i hi
      contrapose hi
      simp only [Finset.mem_union,not_or,Polynomial.notMem_support_iff] at hi
      simp [coeff_C_mul,hi]
    have := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
    have := sparse_bound (a-C t*b)
    dsimp [fiber]; omega
  have cover : positive P ⊆ dirs.biUnion fiber := by
    intro x hx
    obtain ⟨hm,pos⟩ := Finset.mem_filter.mp hx
    have eq := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hm)
    change P.eval x = 0 at eq
    simp only [P,eval_add,eval_pow,eval_mul,eval_C] at eq
    have put (t : ℝ) (ht : t ∈ dirs) (h : a.eval x = t*b.eval x) :
        x ∈ dirs.biUnion fiber := by
      apply Finset.mem_biUnion.mpr
      refine ⟨t,ht,Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots (sub_ne_zero.mpr (fun e => dep ⟨t,e⟩))).mpr ?_),pos⟩⟩
      change (a-C t*b).eval x = 0
      simp [h]
    by_cases by0 : b.eval x = 0
    · have mul : (1+u^3)*(a.eval x)^3 = 0 := by rw [by0] at eq; linarith only [eq]
      have ax : a.eval x = 0 := by simpa using (mul_eq_zero.mp mul).resolve_left lead
      obtain ⟨t,ht⟩ := nonempty
      exact put t ht (by simp [ax,by0])
    · let t := a.eval x / b.eval x
      have ax : a.eval x = t*b.eval x := (div_mul_cancel₀ _ by0).symm
      apply put t _ ax
      apply incl
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots nz).mpr
      change Q.eval t = 0
      simp only [Q,eval_add,eval_C,eval_mul,eval_X,eval_pow]
      dsimp [t]
      field_simp
      linarith only [eq]
  calc
    _ ≤ _ := Finset.card_le_card cover
    _ ≤ ∑ t ∈ dirs, (fiber t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ dirs, 7 := Finset.sum_le_sum (fun t _ => small t)
    _ ≤ 21 := by simp; omega

theorem dependent_three_cubes (a b c : Polynomial ℝ) (u v : ℝ)
    (rel : c = C u*a + C v*b)
    (ha : a.support.card ≤ 4) (hb : b.support.card ≤ 4) (hc : c.support.card ≤ 4) :
    (positive (a^3+b^3+c^3)).card ≤ 21 := by
  by_cases hu : 1+u^3 ≠ 0
  · rw [rel]; exact pencil_chart a b u v ha hb hu
  by_cases hv : 1+v^3 ≠ 0
  · simpa only [rel, add_comm (a^3), add_comm (C u*a)] using
      (pencil_chart b a v u hb ha hv)
  have neg (z : ℝ) (h : ¬ 1+z^3 ≠ 0) : z = -1 := by
    apply (Odd.strictMono_pow (by decide : Odd 3)).injective
    simp only [not_not] at h
    linarith
  have sum0 : a+b+c = 0 := by rw [rel,neg u hu,neg v hv]; simp; ring
  exact (zero_sum_three_cubes a b c sum0 ha hb hc).trans (by decide)

private theorem exponent_split {a b : Polynomial ℝ} {k : ℕ} (h : k ∈ (a*b).support) :
    ∃ i ∈ a.support, ∃ j ∈ b.support, i+j=k := by
  have hn := Polynomial.mem_support_iff.mp h
  rw [coeff_mul] at hn
  obtain ⟨p,mp,nonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact ⟨p.1, Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul nonzero),
    p.2, Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul nonzero),
    Finset.mem_antidiagonal.mp mp⟩

-- No bound on the exponents themselves is required.
theorem four_common_exponents (e : Fin 4 → ℕ) (s : Fin 3 → ℝ)
    (g : Fin 3 → Polynomial ℝ) (h : ∀ i k, k ∈ (g i).support → ∃ j, e j = k) :
    (positive (∑ i, C (s i)*(g i)^3)).card ≤ 19 := by
  classical
  let total (u : Sym (Fin 4) 3) := (u.val.map e).sum
  let exps := Finset.univ.image total
  have count : exps.card ≤ 20 := by
    have up := Finset.card_image_le (f := total) (s := Finset.univ)
    have num : Nat.multichoose 4 3 = 20 := by rw [Nat.multichoose_eq]; decide
    simpa [exps, Sym.card_sym_fin_eq_multichoose, num] using up
  have subset : (∑ i, C (s i)*(g i)^3).support ⊆ exps := by
    intro k hk
    have nonzero := Polynomial.mem_support_iff.mp hk
    rw [finsetSum_coeff] at nonzero
    obtain ⟨i,_,v⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
    rw [coeff_C_mul] at v
    have cub := Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul v)
    rw [pow_succ, pow_two] at cub
    obtain ⟨t,ht,r,hr,rfl⟩ := exponent_split cub
    obtain ⟨p,hp,q,hq,rfl⟩ := exponent_split ht
    obtain ⟨P,rfl⟩ := h i p hp
    obtain ⟨Q,rfl⟩ := h i q hq
    obtain ⟨R,rfl⟩ := h i r hr
    let u : Sym (Fin 4) 3 := ⟨{P,Q,R},by simp⟩
    exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _, by simp [total,u,Nat.add_assoc]⟩
  have sup := (Finset.card_le_card subset).trans count
  have := sparse_bound (∑ i, C (s i)*(g i)^3)
  omega

end VerifiedResults.CubicRoots
