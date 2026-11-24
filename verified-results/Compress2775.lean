import PEqualNP.Defs.NestedCoverCircuit

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

def tag (keep : ℕ → Bool) (start : ℕ) : List Gate → List (Bool × Gate)
  | [] => []
  | g :: gs => (keep start, g) :: tag keep (start + 1) gs

theorem closed_of_reads (keep : ℕ → Bool) (gs : List Gate) (start : ℕ)
    (reads : ∀ j : Fin gs.length, keep (start + j.val) = true →
      ∀ i ∈ gs[j].inputs, i < start + j.val ∧ keep i = true) :
    closed ((List.range start).map keep) (tag keep start gs) := by
  induction gs generalizing start with
  | nil => trivial
  | cons g gs ih =>
    have tail (j : Fin gs.length) (hj : keep (start + 1 + j.val) = true) :
        ∀ i ∈ gs[j].inputs, i < start + 1 + j.val ∧ keep i = true := by
      simpa [Nat.add_assoc, Nat.add_comm 1] using
        reads j.succ (by simpa [Nat.add_assoc, Nat.add_comm 1] using hj)
    have next := ih (start + 1) tail
    rw [List.range_succ, List.map_append, List.map_singleton] at next
    cases h : keep start with
    | false => simpa [tag, h, closed] using next
    | true =>
      simp only [tag, h, closed]
      refine ⟨?_, by simpa [h] using next⟩
      intro i hi
      obtain ⟨hlt, hkeep⟩ := reads ⟨0, by simp⟩ (by simpa using h) i hi
      have lt : i < start := by simpa using hlt
      simp [lt, hkeep]

open PEqualNP.MetaComplexity.NestedCover

def outside (n : ℕ) (T : Finset ℕ) (first second w : ℕ) : Bool :=
  decide (w < n ∨ (w - n ∉ T ∧ w ≠ n + first ∧ w ≠ n + second))

theorem isolated_closed (n : ℕ) (C : Circuit) (T : Finset ℕ) (first second : ℕ)
    (back : ReadsBack n C)
    (iso : ∀ k < C.gates.length, k ∉ T →
      n + first ∉ (gateAt C k).inputs ∧ n + second ∉ (gateAt C k).inputs ∧
      ∀ j ∈ T, n + j ∉ (gateAt C k).inputs) :
    closed ((List.range n).map (outside n T first second))
      (tag (outside n T first second) n C.gates) := by
  apply closed_of_reads
  intro j live i hi
  have g : gateAt C j.val = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD]
  have hj : j.val ∉ T := by
    have h := of_decide_eq_true live
    rcases h with h | ⟨h, _, _⟩
    · omega
    · simpa using h
  have mem : i ∈ (gateAt C j.val).inputs := g ▸ hi
  obtain ⟨hf, hs, ht⟩ := iso j.val j.isLt hj
  refine ⟨back j.val j.isLt i mem, ?_⟩
  apply decide_eq_true
  by_cases h : i < n
  · exact Or.inl h
  · have decomp : n + (i - n) = i := by omega
    exact Or.inr ⟨fun ht' => ht (i-n) ht' (decomp.symm ▸ mem),
      fun e => hf (e ▸ mem), fun e => hs (e ▸ mem)⟩

-- Append one OR gate per remaining leaf, starting from the factored wire.
def chain (start acc : ℕ) : List ℕ → List Gate
  | [] => []
  | i :: rest => ⟨GateOp.or, [acc,i]⟩ :: chain (start+1) start rest

def outputWire (start acc : ℕ) : List ℕ → ℕ
  | [] => acc
  | _ :: rest => outputWire (start+1) start rest

theorem chain_length (xs : List ℕ) (start acc : ℕ) :
    (chain start acc xs).length = xs.length := by
  induction xs generalizing start acc with
  | nil => rfl
  | cons i xs ih => simp [chain, ih]

theorem chain_ordered (xs : List ℕ) (start acc : ℕ) (ha : acc < start)
    (hx : ∀ i ∈ xs, i < start) : orderedAO start (chain start acc xs) := by
  induction xs generalizing start acc with
  | nil => trivial
  | cons i xs ih =>
    have hi := hx i (by simp)
    refine ⟨Or.inr rfl, rfl, ?_, ih _ _ (by omega) (fun j hj => ?_)⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> assumption
    · exact Nat.lt_succ_of_lt (hx j (List.mem_cons_of_mem _ hj))

theorem chain_value (xs : List ℕ) (w : List Bool) (acc : ℕ)
    (hx : ∀ i ∈ xs, i < w.length) :
    (run (chain w.length acc xs) w).getD (outputWire w.length acc xs) false =
      (w.getD acc false || xs.any fun i => w.getD i false) := by
  induction xs generalizing w acc with
  | nil => simp [run, chain, outputWire]
  | cons i xs ih =>
    let b := w.getD acc false || w.getD i false
    let w' := w ++ [b]
    have len : w'.length = w.length + 1 := by simp [w']
    have stay (j : ℕ) (hj : j ∈ xs) : w'.getD j false = w.getD j false := by
      have h := hx j (List.mem_cons_of_mem _ hj)
      simp [w', List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    have t := ih w' w.length (fun j hj => by
      rw [len]
      exact Nat.lt_succ_of_lt (hx j (List.mem_cons_of_mem _ hj)))
    rw [len] at t
    have head : w'.getD w.length false = b := by simp [w', List.getD_eq_getElem?_getD]
    have eq : xs.any (fun j => w'.getD j false) = xs.any (fun j => w.getD j false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor <;> rintro ⟨j,hj,h⟩
      · exact ⟨j,hj,(stay j hj) ▸ h⟩
      · exact ⟨j,hj,(stay j hj).symm ▸ h⟩
    rw [head, eq] at t
    have val : value w ⟨GateOp.or,[acc,i]⟩ = b := by simp [value, GateOp.eval, b]
    simp only [chain, outputWire, run, List.foldl_cons, val]
    change (run (chain (w.length+1) w.length xs) w').getD (outputWire (w.length+1) w.length xs) false = _
    simpa only [b, List.any_cons, Bool.or_assoc] using t

-- Operands and unmerged leaves must name actual retained wires.
theorem rebuild_inputs (n : ℕ) (C : Circuit) (T L : Finset ℕ) (f s : ℕ)
    (back : ReadsBack n C) (tree : IsOrTree n C T L C.output)
    (hf : n+f ∈ L) (hs : n+s ∈ L) (different : f ≠ s)
    (fg : (gateAt C f).op = GateOp.and) (sg : (gateAt C s).op = GateOp.and)
    (iso : ∀ k < C.gates.length, k ∉ T →
      n + f ∉ (gateAt C k).inputs ∧ n + s ∉ (gateAt C k).inputs ∧
      ∀ j ∈ T, n + j ∉ (gateAt C k).inputs) :
    ∀ w, w ∈ (gateAt C f).inputs ∨ w ∈ (gateAt C s).inputs ∨
      w ∈ (L.erase (n+f)).erase (n+s) →
      w < n + C.size ∧ outside n T f s w = true := by
  have realAnd (j : ℕ) (h : (gateAt C j).op = GateOp.and) : j < C.gates.length := by
    by_contra hn
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hn)] at h
  have operand (j w : ℕ) (h : (gateAt C j).op = GateOp.and) (hw : w ∈ (gateAt C j).inputs) :
      w < n+C.size ∧ outside n T f s w = true := by
    have hj := realAnd j h
    have notTree : j ∉ T := by
      intro ht
      have eq := (tree.1 j ht).1
      rw [h] at eq
      contradiction
    obtain ⟨h1,h2,ht⟩ := iso j hj notTree
    refine ⟨(back j hj w hw).trans (Nat.add_lt_add_left hj n), decide_eq_true ?_⟩
    by_cases before : w < n
    · exact Or.inl before
    · have e : n+(w-n) = w := by omega
      exact Or.inr ⟨fun mem => ht (w-n) mem (e.symm ▸ hw),
        fun eq => h1 (eq ▸ hw), fun eq => h2 (eq ▸ hw)⟩
  intro w hw
  rcases hw with h | h | leaf
  · exact operand f w fg h
  · exact operand s w sg h
  obtain ⟨ns,h'⟩ := Finset.mem_erase.mp leaf
  obtain ⟨nf,hl⟩ := Finset.mem_erase.mp h'
  have detached := (tree.2.1 w hl).1
  have nonempty : T ≠ ∅ := by
    intro e
    have only : L = {C.output} := by simpa [e] using tree.2.2.2
    rw [only] at hf hs
    simp only [Finset.mem_singleton] at hf hs
    omega
  obtain ⟨root,hr,output⟩ : ∃ j ∈ T, C.output = n+j := by simpa [nonempty] using tree.2.2.2
  have notRoot : w ≠ C.output := by
    intro e
    exact detached (by simp [e,output,hr])
  have uses : readsIn C T w = 1 := by simpa [notRoot] using (tree.2.1 w hl).2
  have reader : ∃ j ∈ T, w ∈ (gateAt C j).inputs := by
    by_contra! none
    have zero : readsIn C T w = 0 := Finset.sum_eq_zero fun j hj =>
      List.count_eq_zero_of_not_mem (none j hj)
    omega
  obtain ⟨j,hj,hw⟩ := reader
  have bound : j < C.gates.length := by
    by_contra hn
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hn)] at hw
  refine ⟨(back j bound w hw).trans (Nat.add_lt_add_left bound n), decide_eq_true ?_⟩
  by_cases before : w < n
  · exact Or.inl before
  · exact Or.inr ⟨fun ht => detached ⟨by omega, ht⟩, nf, ns⟩

end Compress2775