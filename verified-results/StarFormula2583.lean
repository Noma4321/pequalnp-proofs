import Mathlib.Data.List.Basic
import PEqualNP.Defs.TopForm

namespace VerifiedResults.StarFormula

inductive Tree (V : Type) where
  | input (v : V)
  | either (a b : Tree V)
  | both (a b : Tree V)

def eval (x : V → Bool) : Tree V → Bool
  | .input v => x v
  | .either a b => eval x a || eval x b
  | .both a b => eval x a && eval x b

def cost : Tree V → Nat
  | .input _ => 0
  | .either a b | .both a b => cost a + cost b + 1

-- A trace chooses one child at OR and concatenates both children at AND.
inductive Trace : Tree V → List V → Prop where
  | leaf (v : V) : Trace (.input v) [v]
  | left (h : Trace a vs) : Trace (.either a b) vs
  | right (h : Trace b vs) : Trace (.either a b) vs
  | join (h : Trace a vs) (k : Trace b ws) : Trace (.both a b) (vs ++ ws)

def row (first : V) : List V → Tree V
  | [] => .input first
  | a :: rest => .either (.input a) (row first rest)

theorem row_trace (first v : V) (xs : List V) (h : v = first ∨ v ∈ xs) :
    Trace (row first xs) [v] := by
  induction xs with
  | nil => simp at h; subst v; exact .leaf _
  | cons a xs ih =>
    rcases h with h | h
    · exact .right (ih (Or.inl h))
    · rcases List.mem_cons.mp h with h | h
      · subst v; exact .left (.leaf _)
      · exact .right (ih (Or.inr h))

def star (center first : V) (xs : List V) : Tree V :=
  .both (.input center) (row first xs)

theorem star_trace (center first v : V) (xs : List V) (h : v = first ∨ v ∈ xs) :
    Trace (star center first xs) [center, v] :=
  Trace.join (.leaf center) (row_trace first v xs h)

theorem star_cost (center first : V) (xs : List V) :
    cost (star center first xs) = xs.length + 1 := by
  have aux : cost (row first xs) = xs.length := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [row, cost, ih]
  simp [star, cost, aux]

theorem star_value (x : V → Bool) (center first : V) (xs : List V) :
    eval x (star center first xs) = (x center && (x first || xs.any x)) := by
  have aux : eval x (row first xs) = (x first || xs.any x) := by
    induction xs with
    | nil => simp [row, eval]
    | cons a xs ih => simp [row, eval, ih, Bool.or_left_comm]
  simp [star, eval, aux]

def combine (first : Tree V) : List (Tree V) → Tree V
  | [] => first
  | a :: xs => .either a (combine first xs)

theorem combine_trace (first t : Tree V) (ts : List (Tree V)) (vs : List V)
    (atTree : t = first ∨ t ∈ ts) (w : Trace t vs) :
    Trace (combine first ts) vs := by
  induction ts with
  | nil => simp at atTree; subst t; exact w
  | cons a ts ih =>
    rcases atTree with e | m
    · exact .right (ih (Or.inl e))
    · rcases List.mem_cons.mp m with e | m
      · subst t; exact .left w
      · exact .right (ih (Or.inr m))

theorem combine_cost (first : Tree V) (ts : List (Tree V)) :
    cost (combine first ts) = cost first + (ts.map cost).sum + ts.length := by
  induction ts with
  | nil => simp [combine]
  | cons a ts ih => simp [combine, cost, ih]; omega

theorem combine_value (x : V → Bool) (first : Tree V) (ts : List (Tree V)) :
    eval x (combine first ts) = (eval x first || ts.any (eval x)) := by
  induction ts with
  | nil => simp [combine]
  | cons a ts ih => simp [combine, eval, ih, Bool.or_left_comm]

open PEqualNP.CircuitLowerBounds

def rootWire (base : Nat) : Tree (Fin n) → Nat
  | .input i => i.val
  | .either a b | .both a b => base + cost a + cost b

def emit (base : Nat) : Tree (Fin n) → List Gate
  | .input _ => []
  | .either a b => (emit base a ++ emit (base + cost a) b) ++
      [⟨.or, [rootWire base a, rootWire (base + cost a) b]⟩]
  | .both a b => (emit base a ++ emit (base + cost a) b) ++
      [⟨.and, [rootWire base a, rootWire (base + cost a) b]⟩]

theorem emit_length (t : Tree (Fin n)) (base : Nat) : (emit base t).length = cost t := by
  induction t generalizing base <;> simp_all [emit, cost, Nat.add_assoc]

def circuit (t : Tree (Fin n)) : Circuit := ⟨emit n t, rootWire n t⟩

theorem circuit_size (t : Tree (Fin n)) : (circuit t).size = cost t :=
  emit_length t n

theorem root_bound (t : Tree (Fin n)) {base : Nat} (h : n ≤ base) :
    rootWire base t < base + cost t := by
  cases t with
  | input i => simpa [rootWire, cost] using Nat.lt_of_lt_of_le i.isLt h
  | either a b | both a b => simp [rootWire, cost]; omega

-- At gate position j both operands precede the wire base+j.
theorem emit_ordered (t : Tree (Fin n)) (base : Nat) (h : n ≤ base) :
    ∀ (j : Fin (emit base t).length), ∀ w ∈ ((emit base t)[j.val]).inputs,
      w < base + j.val := by
  induction t generalizing base with
  | input i => intro j; exact Fin.elim0 j
  | either a b ha hb | both a b ha hb =>
    intro j w hw
    have la := emit_length a base
    have lb := emit_length b (base + cost a)
    have hj := j.isLt
    simp only [emit, List.length_append, List.length_cons, List.length_nil] at hj
    by_cases left : j.val < (emit base a).length
    · simp only [emit, List.getElem_append_left (by simp; omega : j.val <
        (emit base a ++ emit (base + cost a) b).length), List.getElem_append_left left] at hw
      exact ha base h ⟨_,left⟩ w hw
    · by_cases middle : j.val < (emit base a ++ emit (base + cost a) b).length
      · simp only [emit, List.getElem_append_left middle,
          List.getElem_append_right (Nat.le_of_not_gt left)] at hw
        have m := hb (base + cost a) (by omega) ⟨j.val - (emit base a).length, by
          simp only [List.length_append] at middle; omega⟩ w hw
        simp only at m
        omega
      · have last : j.val = (emit base a ++ emit (base + cost a) b).length := by
          simp only [List.length_append] at middle ⊢; omega
        simp only [emit, List.getElem_append_right (Nat.le_of_not_gt middle)] at hw
        simp at hw
        have ra := root_bound a h
        have rb := root_bound b (base := base + cost a) (by omega)
        simp only [List.length_append] at last
        rcases hw with rfl | rfl <;> omega

theorem gate_shape (t : Tree (Fin n)) (base : Nat) :
    ∀ g ∈ emit base t, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  induction t generalizing base with
  | input i => simp [emit]
  | either a b ha hb | both a b ha hb =>
    intro g hg
    simp only [emit, List.mem_append, List.mem_singleton] at hg
    rcases hg with (m | m) | rfl
    · exact ha base g m
    · exact hb _ g m
    · simp

theorem circuit_ao2 (t : Tree (Fin n)) : PEqualNP.TopForm.IsAO2 n (circuit t) := by
  refine ⟨fun g hg => (gate_shape t n g hg).1, ?_, fun g hg => (gate_shape t n g hg).2⟩
  intro j hj i hi
  apply emit_ordered t n (Nat.le_refl n) ⟨j,hj⟩ i
  change i ∈ ((emit n t).getD j _).inputs at hi
  change j < (emit n t).length at hj
  rw [List.getD_eq_getElem _ _ hj] at hi
  exact hi

end VerifiedResults.StarFormula
