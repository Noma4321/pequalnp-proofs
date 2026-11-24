import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Defs.LineDegree

namespace Sensitivity2130

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [value g v]) w

theorem preserved (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem value_mono (g : Gate) (hm : g.op = GateOp.and ∨ g.op = GateOp.or)
    (v w : List Bool) (h : ∀ i, v.getD i false = true → w.getD i false = true) :
    value g v = true → value g w = true := by
  rcases hm with ha | ho
  · simp [value, ha, GateOp.eval, List.all_eq_true]
    exact fun hv i hi => h i (hv i hi)
  · simp [value, ho, GateOp.eval, List.any_eq_true]
    intro i hi hv
    exact ⟨i, hi, h i hv⟩

theorem append_lookup (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, Nat.ne_of_lt h]
  · by_cases e : i = w.length
    · subst i
      simp [List.getD_eq_getElem?_getD]
    · simp [e, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show w.length ≤ i by omega), List.getElem?_eq_none (show (w ++ [b]).length ≤ i by simp; omega)]

-- The earliest gate whose value differs must read the changed input directly.
-- Its value on the smaller assignment also bounds its value at baseline.
theorem first_reader (gs : List Gate) (k : ℕ) (base lo hi : List Bool)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (lenB : base.length = lo.length) (lenH : lo.length = hi.length)
    (hb : ∀ i, base.getD i false = true → lo.getD i false = true)
    (hh : ∀ i, lo.getD i false = true → hi.getD i false = true)
    (he : ∀ i, i ≠ k → lo.getD i false = hi.getD i false)
    (changed : ∃ i, i ≠ k ∧ (run gs lo).getD i false ≠ (run gs hi).getD i false) :
    ∃ (j : Fin gs.length), k ∈ gs[j].inputs ∧
      (run gs base).getD (base.length + j.val) false = false ∧
      (run gs hi).getD (hi.length + j.val) false = true := by
  induction gs generalizing base lo hi with
  | nil =>
    obtain ⟨i, hik, hne⟩ := changed
    exact False.elim (hne (he i hik))
  | cons g gs ih =>
    have mono := hm g (by simp)
    have ml := value_mono g mono base lo hb
    have mh := value_mono g mono lo hi hh
    by_cases eq : value g lo = value g hi
    · obtain ⟨j, hj, hjb, hjh⟩ := ih (base ++ [value g base]) (lo ++ [value g lo])
        (hi ++ [value g hi]) (fun a ha => hm a (by simp [ha])) (by simp [lenB])
        (by simp [lenH]) (by
          intro i
          simp only [append_lookup, lenB]
          split <;> first | exact ml | exact hb i) (by
          intro i
          simp only [append_lookup, lenH]
          split <;> first | exact mh | exact hh i) (by
          intro i hik
          simp only [append_lookup, lenH, eq, he i hik]) changed
      refine ⟨j.succ, hj, ?_, ?_⟩
      · simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hjb
      · simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hjh
    · have hread : k ∈ g.inputs := by
        apply Classical.byContradiction
        intro hn
        apply eq
        unfold value
        congr 1
        exact List.map_congr_left fun i him => he i (fun e => hn (e ▸ him))
      have vals : value g base = false ∧ value g hi = true := by
        have step : ∀ a b c : Bool, (a = true → b = true) → (b = true → c = true) →
            b ≠ c → a = false ∧ c = true := by decide
        exact step _ _ _ ml mh eq
      refine ⟨⟨0, by simp⟩, hread, ?_, ?_⟩
      · change (run gs (base ++ [value g base])).getD (base.length + 0) false = false
        rw [Nat.add_zero, preserved _ _ _ (by simp), append_lookup, ite_eq_left rfl, vals.1]
      · change (run gs (hi ++ [value g hi])).getD (hi.length + 0) false = true
        rw [Nat.add_zero, preserved _ _ _ (by simp), append_lookup, ite_eq_left rfl, vals.2]

theorem endpoint_budget (C : Circuit) (hm : Monotone2 C)
    (V : Finset ℕ) (A : Finset (Fin C.size))
    (witness : ∀ k ∈ V, ∃ j ∈ A, k ∈ C.gates[j.val].inputs) :
    V.card ≤ 2 * A.card := by
  let ports (j : Fin C.size) := C.gates[j.val].inputs.toFinset
  have incl : V ⊆ A.biUnion ports := by
    intro k hk
    obtain ⟨j, hj, hread⟩ := witness k hk
    exact Finset.mem_biUnion.mpr ⟨j, hj, List.mem_toFinset.mpr hread⟩
  have bound (j : Fin C.size) (_ : j ∈ A) : (ports j).card ≤ 2 :=
    (List.toFinset_card_le _).trans (hm _ (List.getElem_mem _)).2
  simpa [Nat.mul_comm] using
    (Finset.card_le_card incl).trans (Finset.card_biUnion_le_card_mul A ports 2 bound)

theorem sensitive_inputs (C : Circuit) (n : ℕ) (hm : Monotone2 C)
    (V : Finset ℕ) (A : Finset (Fin C.size))
    (witness : ∀ k ∈ V, ∃ lo hi : List Bool,
      lo.length = n ∧ hi.length = n ∧
      (∀ i, lo.getD i false = true → hi.getD i false = true) ∧
      (∀ i, i ≠ k → lo.getD i false = hi.getD i false) ∧
      C.output ≠ k ∧ C.eval lo ≠ C.eval hi ∧
      ∀ j : Fin C.size,
        (C.wires (List.replicate n false)).getD (n + j.val) false = false →
        (C.wires hi).getD (n + j.val) false = true → j ∈ A) :
    V.card ≤ 2 * A.card := by
  apply endpoint_budget C hm V A
  intro k hk
  obtain ⟨lo, hi, hlen, hlen', hle, heq, hout, hdiff, hA⟩ := witness k hk
  have hbase (i : ℕ) : (List.replicate n false).getD i false = true →
      lo.getD i false = true := by
    by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]
  obtain ⟨j, hread, hzero, hone⟩ := first_reader C.gates k (List.replicate n false) lo hi
    (fun g hg => (hm g hg).1) (by simp [hlen]) (hlen.trans hlen'.symm)
    hbase hle heq ⟨C.output, hout, hdiff⟩
  exact ⟨j, hA j (by simpa only [List.length_replicate, Circuit.wires, run, value] using hzero)
    (by simpa only [hlen', Circuit.wires, run, value] using hone), hread⟩

def pairInput {N : ℕ} (p l : Fin N) (i : Fin (N + N)) : Bool :=
  decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

def pointInput {N : ℕ} (p : Fin N) (i : Fin (N + N)) : Bool :=
  decide (i = Fin.castAdd N p)

def active {N : ℕ} (C : Circuit) (T : Fin N → Finset (Fin N)) : Finset (Fin C.size) :=
  Finset.univ.filter fun j =>
    (C.wires (List.replicate (N + N) false)).getD (N + N + j.val) false = false ∧
    ∃ l, ∃ p ∈ T l, (C.wires (List.ofFn (pairInput p l))).getD (N + N + j.val) false = true

theorem ofFn_lookup {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

theorem sparse_lines (N : ℕ) (C D : Circuit) (T : Fin N → Finset (Fin N))
    (hm : Monotone2 C) (out : D.output = C.output)
    (lost : ∀ l p, p ∈ T l → circuitFun (N + N) C (pairInput p l) = true ∧
      circuitFun (N + N) D (pairInput p l) = false)
    (sound : ∀ p : Fin N, circuitFun (N + N) C (pointInput p) = false)
    (sparse : ∀ l, (T l).card ≤ 22) :
    ∑ l, (T l).card ≤ 44 * (active C T).card := by
  classical
  let L : Finset (Fin N) := Finset.univ.filter fun l => (T l).Nonempty
  let lineWire (l : Fin N) : ℕ := N + l.val
  have inj : Function.Injective lineWire := by
    intro a b h
    exact Fin.ext (Nat.add_left_cancel h)
  have budget := sensitive_inputs C (N + N) hm (L.image lineWire) (active C T) (by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hl).2
    obtain ⟨pos, cut⟩ := lost l p hp
    let hi := List.ofFn (pairInput p l)
    let lo := List.ofFn (pointInput p)
    have klt : lineWire l < N + N := Nat.add_lt_add_left l.isLt N
    have hout : C.output ≠ lineWire l := by
      intro h
      change (run C.gates hi).getD C.output false = true at pos
      change (run D.gates hi).getD D.output false = false at cut
      rw [out, h, preserved _ _ _ (by simpa [hi] using klt)] at cut
      rw [h, preserved _ _ _ (by simpa [hi] using klt), cut] at pos
      contradiction
    refine ⟨lo, hi, by simp [lo], by simp [hi], ?_, ?_, hout, ?_, ?_⟩
    · intro i h
      by_cases hlt : i < N + N
      · change (List.ofFn (pointInput p)).getD i false = true at h
        change (List.ofFn (pairInput p l)).getD i false = true
        rw [ofFn_lookup (pointInput p) ⟨i, hlt⟩] at h
        rw [ofFn_lookup (pairInput p l) ⟨i, hlt⟩]
        simp_all [pointInput, pairInput]
      · simp [lo, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (List.ofFn (pointInput p)).length ≤ i by simpa using Nat.le_of_not_gt hlt)] at h
    · intro i hne
      by_cases hlt : i < N + N
      · change (List.ofFn (pointInput p)).getD i false = (List.ofFn (pairInput p l)).getD i false
        rw [ofFn_lookup (pointInput p) ⟨i, hlt⟩, ofFn_lookup (pairInput p l) ⟨i, hlt⟩]
        have ne : (⟨i, hlt⟩ : Fin (N + N)) ≠ Fin.natAdd N l := fun e => hne (congrArg Fin.val e)
        simp only [pointInput, pairInput, ne, or_false]
      · simp [lo, hi, List.getD_eq_getElem?_getD, hlt]
    · change circuitFun (N + N) C (pointInput p) ≠ circuitFun (N + N) C (pairInput p l)
      simp [sound p, pos]
    · intro j hz hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, l, p, hp, hj⟩)
  rw [Finset.card_image_of_injective _ inj] at budget
  have sumL : ∑ l, (T l).card = ∑ l ∈ L, (T l).card := by
    symm
    apply Finset.sum_subset (Finset.subset_univ L)
    intro i _ h
    have hempty : T i = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun hn => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
    simp [hempty]
  rw [sumL]
  have cap := Finset.sum_le_sum (s := L) (fun i (_ : i ∈ L) => sparse i)
  simp only [Finset.sum_const, smul_eq_mul] at cap
  omega

def lineInput {N : ℕ} (l : Fin N) (i : Fin (N + N)) : Bool :=
  decide (i = Fin.natAdd N l)

def usedPoints {N : ℕ} (T : Fin N → Finset (Fin N)) := Finset.univ.biUnion T

def usedLines {N : ℕ} (T : Fin N → Finset (Fin N)) :=
  Finset.univ.filter fun l => (T l).Nonempty

theorem both_sides (N : ℕ) (C D : Circuit) (T : Fin N → Finset (Fin N))
    (hm : Monotone2 C) (out : D.output = C.output)
    (lost : ∀ l p, p ∈ T l → circuitFun (N + N) C (pairInput p l) = true ∧
      circuitFun (N + N) D (pairInput p l) = false)
    (pointsOff : ∀ l : Fin N, circuitFun (N + N) C (lineInput l) = false)
    (linesOff : ∀ p : Fin N, circuitFun (N + N) C (pointInput p) = false) :
    (usedPoints T).card + (usedLines T).card ≤ 2 * (active C T).card := by
  classical
  let P := (usedPoints T).image Fin.val
  let L := (usedLines T).image (fun l => N + l.val)
  have dis : Disjoint P L := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨l, _, e⟩ := Finset.mem_image.mp hj
    have := p.isLt
    omega
  have bound := sensitive_inputs C (N + N) hm (P ∪ L) (active C T) (by
    intro k hk
    obtain ⟨l, p, hp, kfin, other, ek, es, ep⟩ :
        ∃ l p, p ∈ T l ∧ ∃ kfin other : Fin (N+N),
          k = kfin.val ∧ circuitFun (N+N) C (fun i => decide (i = other)) = false ∧
          ∀ i, pairInput p l i = decide (i = other ∨ i = kfin) := by
      rcases Finset.mem_union.mp hk with h | h
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨l, _, hpl⟩ := Finset.mem_biUnion.mp hp
        exact ⟨l, p, hpl, Fin.castAdd N p, Fin.natAdd N l, rfl, pointsOff l,
          fun i => by simp only [pairInput, or_comm]⟩
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hl).2
        exact ⟨l, p, hp, Fin.natAdd N l, Fin.castAdd N p, rfl, linesOff p, fun _ => rfl⟩
    subst k
    let single (i : Fin (N+N)) := decide (i = other)
    let lo := List.ofFn single
    let hi := List.ofFn (pairInput p l)
    obtain ⟨pos, cut⟩ := lost l p hp
    have hout : C.output ≠ kfin.val := by
      intro e
      change (run C.gates hi).getD C.output false = true at pos
      change (run D.gates hi).getD D.output false = false at cut
      rw [out, e, preserved _ _ _ (by simp [hi])] at cut
      rw [e, preserved _ _ _ (by simp [hi]), cut] at pos
      contradiction
    refine ⟨lo, hi, by simp [lo], by simp [hi], ?_, ?_, hout, ?_, ?_⟩
    · intro i h
      by_cases hlt : i < N + N
      · rw [show lo = _ from rfl, ofFn_lookup single ⟨i, hlt⟩] at h
        change (List.ofFn (pairInput p l)).getD i false = true
        rw [ofFn_lookup (pairInput p l) ⟨i, hlt⟩, ep]
        exact decide_eq_true (Or.inl (of_decide_eq_true h))
      · simp [lo, List.getD_eq_getElem?_getD, hlt] at h
    · intro i ne
      by_cases hlt : i < N + N
      · change (List.ofFn single).getD i false = (List.ofFn (pairInput p l)).getD i false
        rw [ofFn_lookup single ⟨i, hlt⟩, ofFn_lookup (pairInput p l) ⟨i, hlt⟩, ep]
        have ne' : (⟨i, hlt⟩ : Fin (N+N)) ≠ kfin := fun e => ne (congrArg Fin.val e)
        simp only [single, ne', or_false]
      · simp [lo, hi, List.getD_eq_getElem?_getD, hlt]
    · change circuitFun _ C single ≠ circuitFun _ C (pairInput p l)
      rw [pos]
      exact Bool.ne_true_of_eq_false es
    · intro j hz hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, l, p, hp, hj⟩)
  rw [Finset.card_union_of_disjoint dis] at bound
  have inj : Function.Injective (fun l : Fin N => N + l.val) :=
    fun _ _ e => Fin.ext (Nat.add_left_cancel e)
  simpa only [P, L, Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ inj] using bound

theorem sum_over_support {α β : Type*} [Fintype α] [DecidableEq α]
    (S : α → Finset β) (cap : ℕ) (small : ∀ a, (S a).card ≤ cap) :
    ∑ a, (S a).card ≤ cap * (Finset.univ.filter fun a => (S a).Nonempty).card := by
  classical
  calc
    _ ≤ ∑ a, if (S a).Nonempty then cap else 0 := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs with h
      · exact small a
      · simp [Finset.not_nonempty_iff_eq_empty.mp h]
    _ = _ := by simp [← Finset.sum_filter, Nat.mul_comm]

theorem bounded_degrees (N : ℕ) (C D : Circuit) (T : Fin N → Finset (Fin N))
    (hm : Monotone2 C) (out : D.output = C.output)
    (lost : ∀ l p, p ∈ T l → circuitFun (N + N) C (pairInput p l) = true ∧
      circuitFun (N + N) D (pairInput p l) = false)
    (pointsOff : ∀ l : Fin N, circuitFun (N + N) C (lineInput l) = false)
    (linesOff : ∀ p : Fin N, circuitFun (N + N) C (pointInput p) = false)
    (col : ∀ l, (T l).card ≤ 44)
    (row : ∀ p, (Finset.univ.filter fun l => p ∈ T l).card ≤ 44) :
    ∑ l, (T l).card ≤ 44 * (active C T).card := by
  classical
  let S (p : Fin N) := Finset.univ.filter fun l => p ∈ T l
  have support : (Finset.univ.filter fun p => (S p).Nonempty) = usedPoints T := by
    ext p
    simp [S, usedPoints, Finset.Nonempty]
  have swap : ∑ l, (T l).card = ∑ p, (S p).card := by
    calc
      _ = ∑ l, ∑ p : Fin N, if p ∈ T l then 1 else 0 := by
        simp
      _ = ∑ p, ∑ l, if p ∈ T l then 1 else 0 := Finset.sum_comm
      _ = _ := by simp [S]
  have hrow := sum_over_support S 44 row
  rw [support, ← swap] at hrow
  have hcol : ∑ l, (T l).card ≤ 44 * (usedLines T).card := sum_over_support T 44 col
  have hv := both_sides N C D T hm out lost pointsOff linesOff
  omega

theorem plane_point_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l, Fintype.card {p : Fin N // I p l} = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) (p : Fin N) :
    (Finset.univ.filter fun l => I p l).card ≤ q + 1 := by
  classical
  let L := Finset.univ.filter fun l => I p l
  let block := fun l : Fin N => (Finset.univ.filter fun r => I r l).erase p
  have hdis : ∀ l ∈ L, ∀ k ∈ L, l ≠ k → Disjoint (block l) (block k) := by
    intro l hl k hk ne
    apply Finset.disjoint_left.mpr
    intro r hrl hrk
    have hnl := Finset.mem_erase.mp hrl
    have hnk := Finset.mem_erase.mp hrk
    obtain ⟨m, _, hu⟩ := huniq p r (Ne.symm hnl.1)
    exact ne ((hu l ⟨(Finset.mem_filter.mp hl).2, (Finset.mem_filter.mp hnl.2).2⟩).trans
      (hu k ⟨(Finset.mem_filter.mp hk).2, (Finset.mem_filter.mp hnk.2).2⟩).symm)
  have hsize (l : Fin N) (hl : l ∈ L) : (block l).card = q := by
    have hp : p ∈ Finset.univ.filter (fun r => I r l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
    simp [block, Finset.card_erase_of_mem hp, ← Fintype.card_subtype, hcol]
  have incl : L.biUnion block ⊆ Finset.univ.erase p := by
    intro r hr
    obtain ⟨l, _, hb⟩ := Finset.mem_biUnion.mp hr
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hb).1, Finset.mem_univ _⟩
  have hle := Finset.card_le_card incl
  rw [Finset.card_biUnion (fun i hi j hj hij => hdis i hi j hj hij),
    Finset.sum_congr rfl hsize, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hle
  change L.card ≤ q + 1
  apply Nat.le_of_mul_le_mul_right (c := q)
  · simpa [hN, pow_two, Nat.add_mul] using hle
  · omega

theorem desk_through_43 :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   x1 ≤ 43 → (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };               have x13 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x13 x14 : Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x13 ∨ x15 = Fin.natAdd x2 x14);               ∀ (x14 : Fin x2 → Finset (Fin x2)), (∀ (x15 x16 : Fin x2), x16 ∈ x14 x15 → x3 x16 x15 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (x13 x16 x15) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x12 (x13 x16 x15) = Bool.false) → ∑ x16 : Fin x2, (x14 x16).card ≤ (44 : ℕ) * Fintype.card { x16 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x16) Bool.false = Bool.false ∧ ∃ (x17 : Fin x2), ∃ x18 ∈ x14 x17, (x5.wires (List.ofFn (x13 x18 x17))).getD (x2 + x2 + ↑x16) Bool.false = Bool.true } := by
  intro q N I _ C hsmall hq hN hcol huniq hmin sound
  intro D pair T hT
  have separate (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro e
    have he := congrArg Fin.val e
    change p.val = N + l.val at he
    have := p.isLt
    omega
  have lineSound (l : Fin N) := sound (lineInput l) (by
    rw [Fintype.card_subtype]
    have hs : (Finset.univ.filter fun r => lineInput l (Fin.natAdd N r) = true) ⊆ {l} := by
      intro r hr
      have he := of_decide_eq_true (Finset.mem_filter.mp hr).2
      have hv := congrArg Fin.val he
      change N + r.val = N + l.val at hv
      exact Finset.mem_singleton.mpr (Fin.ext (Nat.add_left_cancel hv))
    exact (Finset.card_le_card hs).trans (by rw [Finset.card_singleton]; omega)) (by
      rintro ⟨p, r, _, hp, _⟩
      exact separate p l (of_decide_eq_true hp))
  have pointSound (p : Fin N) := sound (pointInput p) (by
    rw [Fintype.card_subtype]
    simp only [pointInput, decide_eq_true_eq, fun l => (separate p l).symm, Finset.filter_false,
      Finset.card_empty, Nat.zero_le]) (by
      rintro ⟨r, l, _, _, hl⟩
      exact (separate p l).symm (of_decide_eq_true hl))
  have cols (l : Fin N) : (T l).card ≤ 44 := by
    have h := Finset.card_le_card (show T l ⊆ Finset.univ.filter (fun p => I p l) from
      fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hT l p hp).1⟩)
    rw [← Fintype.card_subtype, hcol] at h
    omega
  have rows (p : Fin N) : (Finset.univ.filter fun l => p ∈ T l).card ≤ 44 := by
    have h := Finset.card_le_card (show (Finset.univ.filter fun l => p ∈ T l) ⊆
        Finset.univ.filter (fun l => I p l) from fun l hl =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hT l p (Finset.mem_filter.mp hl).2).1⟩)
    have := plane_point_bound q N I hq hN hcol huniq p
    omega
  rw [Fintype.card_subtype]
  exact bounded_degrees N C D T hmin.1 rfl (fun l p hp => (hT l p hp).2)
    lineSound pointSound cols rows

-- Distinct selected points occur together on at most one selected line.
theorem ordered_pair_count {N : ℕ} (T : Fin N → Finset (Fin N))
    (uniq : ∀ p r : Fin N, p ≠ r → ∀ l k, p ∈ T l → r ∈ T l →
      p ∈ T k → r ∈ T k → l = k) :
    ∑ l, (T l).card * ((T l).card - 1) ≤ (usedPoints T).card * ((usedPoints T).card - 1) := by
  classical
  let P := usedPoints T
  let L (p : Fin N) := Finset.univ.filter fun l => p ∈ T l
  have inside (l : Fin N) : T l ⊆ P :=
    fun _ hp => Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hp⟩
  have pivot (p : Fin N) (hp : p ∈ P) :
      ∑ l ∈ L p, ((T l).card - 1) ≤ P.card - 1 := by
    let block := fun l => (T l).erase p
    have dis : ∀ l ∈ L p, ∀ k ∈ L p, l ≠ k → Disjoint (block l) (block k) := by
      intro l hl k hk hne
      apply Finset.disjoint_left.mpr
      intro r hrl hrk
      exact hne (uniq p r (Finset.mem_erase.mp hrl).1.symm l k
        (Finset.mem_filter.mp hl).2 (Finset.mem_erase.mp hrl).2
        (Finset.mem_filter.mp hk).2 (Finset.mem_erase.mp hrk).2)
    have incl : (L p).biUnion block ⊆ P.erase p := by
      intro r hr
      obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hr
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hl).1, inside l (Finset.mem_erase.mp hl).2⟩
    have e (l : Fin N) (hl : l ∈ L p) : (block l).card = (T l).card - 1 :=
      Finset.card_erase_of_mem (Finset.mem_filter.mp hl).2
    have h := Finset.card_le_card incl
    rwa [Finset.card_biUnion (fun i hi j hj hij => dis i hi j hj hij),
      Finset.sum_congr rfl e, Finset.card_erase_of_mem hp] at h
  calc
    _ = ∑ l : Fin N, ∑ p ∈ P, if p ∈ T l then ((T l).card - 1) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter]
      have eq : P.filter (fun p => p ∈ T l) = T l := by
        ext p
        simp only [Finset.mem_filter, and_iff_right_iff_imp]
        exact fun hp => inside l hp
      simp [eq]
    _ = ∑ p ∈ P, ∑ l ∈ L p, ((T l).card - 1) := by
      rw [Finset.sum_comm]
      simp [L, Finset.sum_filter]
    _ ≤ ∑ _p ∈ P, (P.card - 1) := Finset.sum_le_sum pivot
    _ = _ := by simp [P]

theorem small_point_support {N : ℕ} (T : Fin N → Finset (Fin N))
    (uniq : ∀ p r : Fin N, p ≠ r → ∀ l k, p ∈ T l → r ∈ T l →
      p ∈ T k → r ∈ T k → l = k)
    (small : (usedPoints T).card ≤ 1893) :
    ∑ l, (T l).card ≤ 22 * ((usedPoints T).card + (usedLines T).card) := by
  classical
  let P := (usedPoints T).card
  have tangent (d : ℕ) : 86 * d ≤ d * (d - 1) + (if 0 < d then 1892 else 0) := by
    cases d with
    | zero => decide
    | succ a =>
      simp only [Nat.zero_lt_succ, ite_true, Nat.add_one_sub_one]
      have integer_bound : 86 * ((a : ℤ) + 1) ≤ ((a : ℤ) + 1) * a + 1892 := by
        rcases le_or_gt a 42 with h | h
        · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 42 - a by omega) (show (0 : ℤ) ≤ 43 - a by omega)]
        · nlinarith [mul_nonneg (show (0 : ℤ) ≤ a - 42 by omega) (show (0 : ℤ) ≤ a - 43 by omega)]
      exact_mod_cast integer_bound
  have h := Finset.sum_le_sum (s := Finset.univ) (fun l _ => tangent (T l).card)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at h
  have c : (∑ l : Fin N, if 0 < (T l).card then 1892 else 0 : ℕ) =
      (usedLines T).card * 1892 := by
    simp [usedLines, Finset.card_pos, ← Finset.sum_filter]
  rw [c] at h
  have b := ordered_pair_count T uniq
  have hp := Nat.mul_le_mul_left P (show P - 1 ≤ 1892 by dsimp [P]; omega)
  change _ ≤ P * (P - 1) at b
  change _ ≤ 22 * (P + _)
  omega

theorem few_vertices (N : ℕ) (C D : Circuit) (T : Fin N → Finset (Fin N))
    (hm : Monotone2 C) (out : D.output = C.output)
    (lost : ∀ l p, p ∈ T l → circuitFun (N + N) C (pairInput p l) = true ∧
      circuitFun (N + N) D (pairInput p l) = false)
    (pointsOff : ∀ l : Fin N, circuitFun (N + N) C (lineInput l) = false)
    (linesOff : ∀ p : Fin N, circuitFun (N + N) C (pointInput p) = false)
    (uniq : ∀ p r : Fin N, p ≠ r → ∀ l k, p ∈ T l → r ∈ T l →
      p ∈ T k → r ∈ T k → l = k)
    (small : (usedPoints T).card ≤ 1893 ∨ (usedLines T).card ≤ 1893) :
    ∑ l, (T l).card ≤ 44 * (active C T).card := by
  classical
  have budget := both_sides N C D T hm out lost pointsOff linesOff
  rcases small with hp | hl
  · have := small_point_support T uniq hp
    omega
  let S (p : Fin N) := Finset.univ.filter fun l => p ∈ T l
  have dual (l k : Fin N) (hne : l ≠ k) (p r : Fin N)
      (a : l ∈ S p) (b : k ∈ S p) (c : l ∈ S r) (d : k ∈ S r) : p = r := by
    by_contra h
    exact hne (uniq p r h l k (Finset.mem_filter.mp a).2 (Finset.mem_filter.mp c).2
      (Finset.mem_filter.mp b).2 (Finset.mem_filter.mp d).2)
  have sl : usedPoints S = usedLines T := by
    ext l
    constructor
    · intro h
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, (Finset.mem_filter.mp hp).2⟩
    · intro h
      obtain ⟨p, hp⟩ := (Finset.mem_filter.mp h).2
      exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  have sp : usedLines S = usedPoints T := by
    ext p
    simp [S, usedPoints, usedLines, Finset.Nonempty]
  have swap : ∑ l, (T l).card = ∑ p, (S p).card := by
    calc
      _ = ∑ l, ∑ p : Fin N, if p ∈ T l then 1 else 0 := by simp
      _ = ∑ p, ∑ l, if p ∈ T l then 1 else 0 := Finset.sum_comm
      _ = _ := by simp [S]
  have h := small_point_support S dual (by rwa [sl])
  rw [sl, sp, ← swap] at h
  omega

end Sensitivity2130
