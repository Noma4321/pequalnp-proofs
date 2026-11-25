import Mathlib.Data.List.Basic
import PEqualNP.Defs.TopForm
import PEqualNP.Defs.ReadK

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

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem run_ext (gs : List Gate) (w : List Bool) :
    ∃ s, gs.foldl step w = w ++ s ∧ s.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨s, eq, len⟩ := ih (step w g)
    exact ⟨_ :: s, by simpa [step, List.append_assoc] using eq, by simp [len]⟩

private theorem keep (w s : List Bool) (i : Nat) (h : i < w.length) :
    (w ++ s).getD i false = w.getD i false := by
  simp [List.getElem?_append_left h]

private theorem last_step (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step]

private theorem run_value (x : Fin n → Bool) (t : Tree (Fin n)) (w : List Bool)
    (base : Nat) (len : w.length = base) (enough : n ≤ base)
    (inputs : ∀ i : Fin n, w.getD i.val false = x i) :
    ((emit base t).foldl step w).getD (rootWire base t) false = eval x t := by
  induction t generalizing w base with
  | input i => exact inputs i
  | either a b ha hb | both a b ha hb =>
    let wa := (emit base a).foldl step w
    let wb := (emit (base + cost a) b).foldl step wa
    obtain ⟨sa, ea, la⟩ := run_ext (emit base a) w
    obtain ⟨sb, eb, lb⟩ := run_ext (emit (base + cost a) b) wa
    change wa = w ++ sa at ea
    change wb = wa ++ sb at eb
    have lena : wa.length = base + cost a := by rw [ea, List.length_append, la, emit_length, len]
    have lenb : wb.length = base + cost a + cost b := by rw [eb, List.length_append, lb, emit_length, lena]
    have va := ha w base len enough inputs
    change wa.getD _ _ = _ at va
    have left : wb.getD (rootWire base a) false = eval x a := by
      rw [eb, keep, va]
      rw [lena]; exact root_bound a enough
    have right := hb wa (base + cost a) lena (by omega) (fun i => by
      rw [ea, keep, inputs]; omega)
    change wb.getD _ _ = _ at right
    simp only [emit, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (step wb _).getD (base + cost a + cost b) false = _
    rw [← lenb, last_step]
    simp only [List.map_cons, List.map_nil, left, right, GateOp.eval, eval,
      List.any_cons, List.all_cons, List.any_nil, List.all_nil, id_eq,
      Bool.or_false, Bool.and_true]

theorem circuit_value (x : Fin n → Bool) (t : Tree (Fin n)) :
    (circuit t).eval (List.ofFn x) = eval x t := by
  apply run_value x t (List.ofFn x) n (by simp) (Nat.le_refl n)
  intro i
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

open PEqualNP.ReadK
private abbrev Vectors := List (List Nat)
private def vop (S : List Nat) (op : GateOp) (ins : List Vectors) : Vectors :=
  match op with
  | .or => ins.foldl (fun acc a => a.foldl insertNew acc) []
  | .and => ins.foldl (andStep 1) [S.map fun _ => 0]
  | _ => []
private def vstep (S : List Nat) (w : List Vectors) (g : Gate) :=
  w ++ [vop S g.op (g.inputs.map fun i => w.getD i [])]
private def treeVectors (S : List Nat) (x : Fin n → Vectors) : Tree (Fin n) → Vectors
  | .input i => x i
  | .either a b => vop S .or [treeVectors S x a, treeVectors S x b]
  | .both a b => vop S .and [treeVectors S x a, treeVectors S x b]

private theorem vector_ext (S : List Nat) (gs : List Gate) (w : List Vectors) :
    ∃ s, gs.foldl (vstep S) w = w ++ s ∧ s.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨s, eq, len⟩ := ih (vstep S w g)
    exact ⟨_ :: s, by simpa [vstep, List.append_assoc] using eq, by simp [len]⟩

private theorem vector_keep (w s : List Vectors) (i : Nat) (h : i < w.length) :
    (w ++ s).getD i [] = w.getD i [] := by
  simp [List.getElem?_append_left h]

private theorem last_vector (S : List Nat) (w : List Vectors) (g : Gate) :
    (vstep S w g).getD w.length [] = vop S g.op (g.inputs.map fun i => w.getD i []) := by
  simp [vstep]

private theorem vector_run (S : List Nat) (x : Fin n → Vectors) (t : Tree (Fin n)) (w : List Vectors)
    (base : Nat) (len : w.length = base) (enough : n ≤ base)
    (inputs : ∀ i : Fin n, w.getD i.val [] = x i) :
    ((emit base t).foldl (vstep S) w).getD (rootWire base t) [] = treeVectors S x t := by
  induction t generalizing w base with
  | input i => exact inputs i
  | either a b ha hb | both a b ha hb =>
    let wa := (emit base a).foldl (vstep S) w
    let wb := (emit (base + cost a) b).foldl (vstep S) wa
    obtain ⟨sa, ea, la⟩ := vector_ext S (emit base a) w
    obtain ⟨sb, eb, lb⟩ := vector_ext S (emit (base + cost a) b) wa
    change wa = w ++ sa at ea
    change wb = wa ++ sb at eb
    have lena : wa.length = base + cost a := by rw [ea, List.length_append, la, emit_length, len]
    have lenb : wb.length = base + cost a + cost b := by rw [eb, List.length_append, lb, emit_length, lena]
    have va := ha w base len enough inputs
    change wa.getD _ _ = _ at va
    have left : wb.getD (rootWire base a) [] = treeVectors S x a := by
      rw [eb, vector_keep, va]
      rw [lena]; exact root_bound a enough
    have right := hb wa (base + cost a) lena (by omega) (fun i => by
      rw [ea, vector_keep, inputs]; omega)
    change wb.getD _ _ = _ at right
    simp only [emit, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (vstep S wb _).getD (base + cost a + cost b) [] = _
    rw [← lenb, last_vector]
    simp only [List.map_cons, List.map_nil, left, right, treeVectors]

private theorem union_mem (v : List Nat) (xs ys : Vectors) :
    v ∈ xs.foldl insertNew ys ↔ v ∈ ys ∨ v ∈ xs := by
  have one (a : List Nat) (acc : Vectors) : v ∈ insertNew acc a ↔ v ∈ acc ∨ v = a := by
    by_cases h : a ∈ acc
    · simp [insertNew, h, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ h)]
    · simp [insertNew, h]
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih => simp [ih, one, or_assoc]

private theorem product_mem (u v : List Nat) {A B : Vectors}
    (hu : u ∈ A) (hv : v ∈ B) : capAdd 1 u v ∈ andStep 1 A B := by
  unfold andStep
  apply (union_mem ..).mpr
  exact Or.inr (List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr ⟨v,hv,rfl⟩⟩)

private def counts (S vs : List Nat) := S.map fun i => min (vs.count i) 2

private theorem count_join (S a b : List Nat) :
    capAdd 1 (counts S a) (counts S b) = counts S (a ++ b) := by
  induction S with
  | nil => rfl
  | cons i S ih =>
    change _ :: capAdd 1 (counts S a) (counts S b) = _ :: counts S (a ++ b)
    congr 1
    · simp only [List.count_append]; omega

private theorem trace_vector {t : Tree (Fin n)} {vs : List (Fin n)} (tr : Trace t vs)
    (S : List Nat) (members : ∀ i ∈ vs, i.val ∈ S) :
    counts S (vs.map Fin.val) ∈ treeVectors S (fun i => leafVectors S 1 i.val) t := by
  induction tr with
  | leaf i =>
    have hi := members i (by simp)
    simp only [treeVectors, leafVectors, hi, ↓reduceIte, counts, List.map_cons, List.map_nil,
      List.mem_singleton]
    apply List.map_congr_left
    intro j _
    by_cases eq : j = i.val
    · simp [eq]
    · simp [eq, Ne.symm eq]
  | left _ ih =>
    simpa [treeVectors, vop, union_mem] using
      (Or.inl (ih members) : _ ∨ _)
  | right _ ih =>
    simpa [treeVectors, vop, union_mem] using
      (Or.inr (ih members) : _ ∨ _)
  | @join a vs b ws ta tb ha hb =>
    have va := ha (fun i hi => members i (List.mem_append_left _ hi))
    have vb := hb (fun i hi => members i (List.mem_append_right _ hi))
    have z : counts S [] ∈ [S.map fun _ => 0] := by simp [counts]
    have p := product_mem _ _ (product_mem _ _ z va) vb
    simpa [treeVectors, vop, count_join, List.map_append] using p

theorem compiled_reads_once {t : Tree (Fin n)} {vs : List (Fin n)}
    (tr : Trace t vs) (S : List Nat) (members : ∀ i ∈ vs, i.val ∈ S)
    (once : ∀ i ∈ S, (vs.map Fin.val).count i ≤ 1) :
    readsAtMost (circuit t) n S 1 = true := by
  apply List.any_eq_true.mpr
  refine ⟨counts S (vs.map Fin.val), ?_, ?_⟩
  · have eq := vector_run S (fun i : Fin n => leafVectors S 1 i.val) t
      ((List.range n).map (leafVectors S 1)) n (by simp) (Nat.le_refl _)
      (fun i => by rw [List.getD_eq_getElem _ _ (by simp)]; simp)
    change _ ∈ ((emit n t).foldl (vstep S) _).getD (rootWire n t) []
    rw [eq]
    exact trace_vector tr S members
  · apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact decide_eq_true ((Nat.min_le_left _ _).trans (once i hi))

theorem compiled_edge {t : Tree (Fin n)} {u v : Fin n} (different : u ≠ v)
    (tr : Trace t [u,v]) :
    readsAtMost (circuit t) n (setList {u,v}) 1 = true := by
  apply compiled_reads_once tr
  · intro i hi
    apply List.mem_map.mpr
    refine ⟨i, List.mem_filter.mpr ⟨by simp, ?_⟩, rfl⟩
    simpa using hi
  · intro i _
    have ne : u.val ≠ v.val := fun h => different (Fin.ext h)
    by_cases hu : u.val = i <;> by_cases hv : v.val = i <;>
      simp_all

theorem incidence_read_one {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (t : Tree (Fin (N+N)))
    (value : ∀ z, eval z t = decide (∃ p l, I p l ∧
      z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (traces : ∀ p l, I p l → Trace t [Fin.castAdd N p, Fin.natAdd N l]) :
    IsReadK (N+N) (circuit t) 1 := by
  intro S prime
  have spec (U : Finset (Fin (N+N))) :
      PEqualNP.MetaComplexity.circuitFun (N+N) (circuit t) (setInput U) =
        decide (∃ p l, I p l ∧ setInput U (Fin.castAdd N p) = true ∧
          setInput U (Fin.natAdd N l) = true) :=
    (circuit_value _ _).trans (value _)
  obtain ⟨onS, minimal⟩ := prime
  rw [spec] at onS
  obtain ⟨p,l,h, hp,hl⟩ := of_decide_eq_true onS
  let E : Finset (Fin (N+N)) := {Fin.castAdd N p, Fin.natAdd N l}
  have sub : E ⊆ S := by
    intro i hi
    rcases Finset.mem_insert.mp hi with e | e
    · exact e ▸ of_decide_eq_true hp
    · exact (Finset.mem_singleton.mp e) ▸ of_decide_eq_true hl
  have eq : E = S := by
    by_contra ne
    have off := minimal E (Finset.mem_ssubsets.mpr (ssubset_of_subset_of_ne sub ne))
    rw [spec] at off
    exact (of_decide_eq_false off) ⟨p,l,h, by simp [E, setInput], by simp [E, setInput]⟩
  rw [← eq]
  apply compiled_edge _ (traces p l h)
  intro eq
  have contra := congrArg Fin.val eq
  simp at contra
  omega

private theorem uniform_or {A V : Type} (f : A → Tree V) (xs : List A) (ne : xs ≠ [])
    (d : Nat) (size : ∀ a ∈ xs, cost (f a) = d) :
    ∃ t, cost t + 1 = xs.length * (d+1) ∧
      (∀ x, eval x t = true ↔ ∃ a ∈ xs, eval x (f a) = true) ∧
      (∀ a ∈ xs, ∀ vs, Trace (f a) vs → Trace t vs) := by
  induction xs with
  | nil => exact (ne rfl).elim
  | cons a xs ih =>
    by_cases empty : xs = []
    · subst xs
      refine ⟨f a, by simp [size], ?_, ?_⟩
      · simp
      · simp
    · obtain ⟨tail, count, val, traces⟩ := ih empty (fun b hb => size b (by simp [hb]))
      refine ⟨.either (f a) tail, ?_, ?_, ?_⟩
      · simp only [cost, List.length_cons, Nat.add_mul, Nat.one_mul]
        have h := size a (by simp)
        omega
      · intro x
        simp [eval, val]
      · intro b hb vs tr
        rcases List.mem_cons.mp hb with e | m
        · subst b; exact .left tr
        · exact .right (traces b m vs tr)

theorem incidence_star_tree (N q : Nat) (hN : 0 < N) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) :
    ∃ t : Tree (Fin (N+N)), cost t + 1 = N * (q+2) ∧
      (∀ z, eval z t = decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
      (∀ p l, I p l → Trace t [Fin.castAdd N p, Fin.natAdd N l]) := by
  classical
  have line (l : Fin N) : ∃ t : Tree (Fin (N+N)), cost t = q+1 ∧
      (∀ z, eval z t = true ↔ ∃ p, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ p, I p l → Trace t [Fin.castAdd N p, Fin.natAdd N l]) := by
    let ps := (Finset.univ.filter (fun p => I p l)).toList
    have len : ps.length = q+1 := by simpa [ps] using degree l
    have mem (p : Fin N) : p ∈ ps ↔ I p l := by simp [ps]
    obtain ⟨r, count, val, tr⟩ := uniform_or
      (fun p : Fin N => Tree.input (Fin.castAdd N p)) ps (by intro e; simp [e] at len)
      0 (fun _ _ => rfl)
    refine ⟨.both r (.input (Fin.natAdd N l)), ?_, ?_, ?_⟩
    · simpa [cost, len] using count
    · intro z
      simp [eval, val, mem]
      exact ⟨fun ⟨⟨p,h,hp⟩,hl⟩ => ⟨p,h,hp,hl⟩, fun ⟨p,h,hp,hl⟩ => ⟨⟨p,h,hp⟩,hl⟩⟩
    · intro p hp
      exact Trace.join (tr p ((mem p).mpr hp) _ (.leaf _)) (.leaf _)
  choose f size val traces using line
  obtain ⟨t,count,truth,tr⟩ := uniform_or f (List.finRange N)
    (by intro e; have := congrArg List.length e; simp_all) (q+1) (fun a _ => size a)
  refine ⟨t, by simpa using count, ?_, ?_⟩
  · intro z
    apply Bool.eq_iff_iff.mpr
    simp only [truth, List.mem_finRange, true_and, val, decide_eq_true_eq]
    exact ⟨fun ⟨l,p,h⟩ => ⟨p,l,h⟩, fun ⟨p,l,h⟩ => ⟨l,p,h⟩⟩
  · intro p l inc
    exact tr l (by simp) _ (traces l p inc)

theorem replacement_of_budget {N q : Nat} (hN : 0 < N) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (C : Circuit) (budget : N*(q+2) ≤ C.size+1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N+N) D ∧
      (∀ z, PEqualNP.MetaComplexity.circuitFun (N+N) D z = decide
        (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (N+N) D 1 := by
  obtain ⟨t, count, value, traces⟩ := incidence_star_tree N q hN I degree
  exact ⟨circuit t, circuit_ao2 t, fun z => (circuit_value z t).trans (value z),
    by rw [circuit_size]; omega, incidence_read_one I t value traces⟩

end VerifiedResults.StarFormula
