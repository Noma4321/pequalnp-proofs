import Mathlib.Data.List.Basic

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

end VerifiedResults.StarFormula
