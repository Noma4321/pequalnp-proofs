import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_4754

def wire (i : ℕ) : ℕ :=
  if i < 16 then if i = 10 then 17 else if i = 15 then 16 else i else i + 2

def copyGate (g : Gate) : Gate := ⟨g.op, g.inputs.map wire⟩

def merge : Gate := ⟨GateOp.or, [10,15]⟩

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, Nat.ne_of_lt h]
  · by_cases e : i = w.length
    · subst i
      simp [List.getD_eq_getElem?_getD]
    · have big : (w ++ [b]).length ≤ i := by simp; omega
      simp [e,List.getD_eq_getElem?_getD,List.getElem?_eq_none big,
        List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem wire_bound (i j : ℕ) (h : i < 16+j) : wire i < 18+j := by
  unfold wire
  split_ifs <;> omega

theorem simulate (gs : List Gate) (v w : List Bool) (hv : 16 ≤ v.length)
    (hlen : w.length = v.length + 2)
    (h : ∀ i, w.getD (wire i) false = v.getD i false) :
    ∀ i, ((gs.map copyGate).foldl step w).getD (wire i) false =
      (gs.foldl step v).getD i false := by
  induction gs generalizing v w with
  | nil => exact h
  | cons g gs ih =>
    have val : (copyGate g).op.eval ((copyGate g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      simp only [copyGate, List.map_map, Function.comp_def, h]
    apply ih (step v g) (step w (copyGate g))
    · simp [step]; omega
    · simp [step,hlen]
    · intro i
      simp only [step,snoc,val,h]
      have iff : wire i = w.length ↔ i = v.length := by
        unfold wire
        split_ifs <;> omega
      simp only [iff]

end PEqualNP.Outside.L_meta_4754

open PEqualNP.Outside.L_meta_4754

theorem PEqualNP.Outside.L_meta_4754 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (17 : ℕ) x4 ∧ x4.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x5 : Fin (17 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x4 x5 = PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x1 fun (x6 : Fin (16 : ℕ)) => if x6 = (10 : Fin (16 : ℕ)) then x5 (10 : Fin (17 : ℕ)) || x5 (15 : Fin (17 : ℕ)) else if x6 = (15 : Fin (16 : ℕ)) then x5 (16 : Fin (17 : ℕ)) else x5 (Fin.ofNat (17 : ℕ) ↑x6) := by
  intro C hm hb
  let D : Circuit := ⟨merge :: C.gates.map copyGate, wire C.output⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | h
    · exact ⟨Or.inr rfl, by decide⟩
    · obtain ⟨g,mem,rfl⟩ := List.mem_map.mp h
      simpa [copyGate] using hm g mem
  · intro j hj i hi
    cases j with
    | zero =>
      change i ∈ [10,15] at hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      omega
    | succ k =>
      have hk : k < C.gates.length := by simpa [D] using hj
      have newGate : gateAt D (k+1) = copyGate C.gates[k] := by
        simp [gateAt,D,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk]
      rw [newGate] at hi
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
      have oldGate : gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk
      have bound := wire_bound a k (hb k hk a (oldGate.symm ▸ ha))
      omega
  · simp [D,Circuit.size]
  · intro x
    let y (i : Fin 16) := if i = 10 then x 10 || x 15 else if i = 15 then x 16 else x (Fin.ofNat 17 i.val)
    let w := step (List.ofFn x) merge
    have h (i : ℕ) : w.getD (wire i) false = (List.ofFn y).getD i false := by
      by_cases hi : i < 16
      · interval_cases i <;> first | rfl | change (x 10 || (x 15 || false)) = (x 10 || x 15); simp
      · have hw : w.length ≤ wire i := by simp [w, step, wire, hi]; omega
        have hv : (List.ofFn y).length ≤ i := by simpa using Nat.le_of_not_gt hi
        simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none hw,List.getElem?_eq_none hv,Option.getD_none]
    exact simulate C.gates (List.ofFn y) w (by simp) (by simp [w,step]) h C.output