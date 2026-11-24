import PEqualNP.Defs.CircuitLowerBounds

namespace Compress2775

open PEqualNP.CircuitLowerBounds

-- One flag per old wire. The new index counts earlier retained wires.
def rank (keep : List Bool) (i : ℕ) := ((keep.take i).filter id).length

def select : List Bool → List Bool → List Bool
  | k :: ks, b :: bs => if k then b :: select ks bs else select ks bs
  | _, _ => []

theorem retained_value (ks bs : List Bool) (len : ks.length = bs.length)
    (i : ℕ) (live : ks[i]? = some true) :
    (select ks bs).getD (rank ks i) false = bs.getD i false := by
  induction ks generalizing bs i with
  | nil => simp at live
  | cons k ks ih =>
    cases bs with
    | nil => simp at len
    | cons b bs =>
      have hlen : ks.length = bs.length := by simpa using len
      cases i with
      | zero =>
        have hk : k = true := by simpa using live
        simp [hk, select, rank]
      | succ i =>
        have h := ih bs hlen i (by simpa using live)
        cases k <;> simpa [select, rank, List.getD_eq_getElem?_getD] using h

theorem select_snoc (ks bs : List Bool) (len : ks.length = bs.length) (k b : Bool) :
    select (ks ++ [k]) (bs ++ [b]) = select ks bs ++ (if k then [b] else []) := by
  induction ks generalizing bs with
  | nil =>
    have : bs = [] := List.length_eq_zero_iff.mp (by simpa using len.symm)
    subst bs
    cases k <;> rfl
  | cons a ks ih =>
    cases bs with
    | nil => simp at len
    | cons x bs =>
      cases a <;> simp [select, ih bs (by simpa using len)]

def value (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun bs g => bs ++ [value bs g]) w

def compile (ks : List Bool) : List (Bool × Gate) → List Gate
  | [] => []
  | (true,g) :: gs => ⟨g.op, g.inputs.map (rank ks)⟩ :: compile (ks ++ [true]) gs
  | (false,_) :: gs => compile (ks ++ [false]) gs

def closed (ks : List Bool) : List (Bool × Gate) → Prop
  | [] => True
  | (true,g) :: gs => (∀ i ∈ g.inputs, ks[i]? = some true) ∧ closed (ks ++ [true]) gs
  | (false,_) :: gs => closed (ks ++ [false]) gs

-- Kept gates may be interspersed with arbitrarily many discarded gates.
theorem compile_correct (gs : List (Bool × Gate)) (ks bs : List Bool)
    (len : ks.length = bs.length) (safe : closed ks gs) :
    run (compile ks gs) (select ks bs) =
      select (ks ++ gs.map Prod.fst) (run (gs.map Prod.snd) bs) := by
  induction gs generalizing ks bs with
  | nil => simp [run, compile]
  | cons tag gs ih =>
    obtain ⟨k,g⟩ := tag
    cases k with
    | false =>
      have h := ih (ks ++ [false]) (bs ++ [value bs g]) (by simp [len]) safe
      simpa [compile, run, select_snoc ks bs len] using h
    | true =>
      have same : value (select ks bs) ⟨g.op, g.inputs.map (rank ks)⟩ = value bs g := by
        unfold value
        simp only [List.map_map, Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact retained_value ks bs len i (safe.1 i hi)
      have h := ih (ks ++ [true]) (bs ++ [value bs g]) (by simp [len]) safe.2
      simpa [compile, run, select_snoc ks bs len, same] using h

theorem compile_length (gs : List (Bool × Gate)) (ks : List Bool) :
    (compile ks gs).length = (gs.filter Prod.fst).length := by
  induction gs generalizing ks with
  | nil => rfl
  | cons tag gs ih => obtain ⟨k,g⟩ := tag; cases k <;> simp [compile, ih]

theorem rank_lt (ks : List Bool) (i : ℕ) (live : ks[i]? = some true) :
    rank ks i < (ks.filter id).length := by
  induction ks generalizing i with
  | nil => simp at live
  | cons k ks ih =>
    cases i with
    | zero =>
      have hk : k = true := by simpa using live
      simp [hk, rank]
    | succ i =>
      have h := ih i (by simpa using live)
      cases k <;> simpa [rank] using h

def orderedAO (n : ℕ) : List Gate → Prop
  | [] => True
  | g :: gs => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
      (∀ i ∈ g.inputs, i < n) ∧ orderedAO (n+1) gs

theorem compile_ordered (gs : List (Bool × Gate)) (ks : List Bool) (safe : closed ks gs)
    (ao : ∀ g ∈ gs.map Prod.snd, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    orderedAO (ks.filter id).length (compile ks gs) := by
  induction gs generalizing ks with
  | nil => trivial
  | cons tag gs ih =>
    obtain ⟨k,g⟩ := tag
    have tail : ∀ a ∈ gs.map Prod.snd, (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length = 2 :=
      fun a ha => ao a (List.mem_cons_of_mem _ ha)
    cases k with
    | false => simpa [compile] using ih (ks ++ [false]) safe tail
    | true =>
      obtain ⟨op, arity⟩ := ao g (by simp)
      refine ⟨op, by simpa using arity, ?_, ?_⟩
      · intro i hi
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
        exact rank_lt ks j (safe.1 j hj)
      · simpa using ih (ks ++ [true]) safe.2 tail

end Compress2775