import PEqualNP.Defs.MetaComplexityLgpMono

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem packed_eval (w : ℕ) (C : Circuit) (xs : List (BitVec w)) (r : Fin w)
    (hmono : Monotone2 C) :
    let ws := C.gates.foldl (fun (v : List (BitVec w)) g =>
      let args := g.inputs.map fun i => v.getD i 0
      v ++ [if g.op.eval [] then args.foldr (· &&& ·) (BitVec.allOnes w)
            else args.foldr (· ||| ·) 0]) xs
    (ws.getD C.output 0).getLsbD r.val = C.eval (xs.map fun m => m.getLsbD r.val) := by
  let bit := fun m : BitVec w => m.getLsbD r.val
  have lookup (v : List (BitVec w)) (i : ℕ) :
      (v.map bit).getD i false = bit (v.getD i 0) := by
    induction v generalizing i with
    | nil => simp [bit]
    | cons a v ih => cases i with
      | zero => rfl
      | succ j => exact ih j
  have conj (v : List (BitVec w)) :
      bit (v.foldr (· &&& ·) (BitVec.allOnes w)) = (v.map bit).all id := by
    induction v with
    | nil => simp [bit]
    | cons a v ih => simpa [bit] using congrArg (fun b => bit a && b) ih
  have disj (v : List (BitVec w)) :
      bit (v.foldr (· ||| ·) 0) = (v.map bit).any id := by
    induction v with
    | nil => simp [bit]
    | cons a v ih => simpa [bit] using congrArg (fun b => bit a || b) ih
  let step (v : List (BitVec w)) (g : Gate) :=
    let args := g.inputs.map fun i => v.getD i 0
    v ++ [if g.op.eval [] then args.foldr (· &&& ·) (BitVec.allOnes w)
          else args.foldr (· ||| ·) 0]
  let scalar (v : List Bool) (g : Gate) :=
    v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
  have stepEq (v : List (BitVec w)) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
      (step v g).map bit = scalar (v.map bit) g := by
    rcases hg with ha | ho
    · simp only [step, scalar, ha, GateOp.eval, List.all_nil, ite_true,
        List.map_append, List.map_cons, List.map_nil, conj, List.map_map, Function.comp_def, lookup]
    · simp only [step, scalar, ho, GateOp.eval, List.any_nil, Bool.false_eq_true, ite_false,
        List.map_append, List.map_cons, List.map_nil, disj, List.map_map, Function.comp_def, lookup]
  have sim (gs : List Gate) (v : List (BitVec w))
      (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      (gs.foldl step v).map bit = gs.foldl scalar (v.map bit) := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih _ (fun a ha => hm a (List.mem_cons_of_mem _ ha)), stepEq _ _ (hm g (by simp))]
  change bit ((C.gates.foldl step xs).getD C.output 0) =
    (C.gates.foldl scalar (xs.map bit)).getD C.output false
  rw [← lookup, sim _ _ (fun g hg => (hmono g hg).1)]
