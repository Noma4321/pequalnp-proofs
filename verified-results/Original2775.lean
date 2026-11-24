import PEqualNP.Defs.TopForm
import Mathlib.Data.Finset.Max

namespace Original2775
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- Tree propagation and wire evaluation below are adapted from the project's
-- L_meta_536.lean. Its helper lemmas are reproduced to keep the dependency
-- on the definitions library only.
variable {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
lemma vO (b:IsOrTree n C G L ρ) {w:ℕ}
  (f:w∈L∨∃j∈G,w=n+j) (a:w≠ρ):
  ∃j∈G,w∈(gateAt C j).inputs:=by
 have g:readsIn C G w=1:=by
  rcases f with e|⟨j,c,rfl⟩
  ·simpa[a] using(b.2.1 w e).2
  ·simpa[a] using b.2.2.1 j c
 by_contra d
 push Not at d
 have h:readsIn C G w=0:=Finset.sum_eq_zero (fun j c=>List.count_eq_zero_of_not_mem (d j c));omega
lemma pI (p:IsOrTree n C G L ρ)
  (d:ReadsBack n C) (q:∀j∈G,j<C.gates.length)
  (P:ℕ→Prop)
  (e:∀j∈G,∀w∈(gateAt C j).inputs,P w→P (n+j))
  {i:ℕ} (r:i∈L∨∃j∈G,i=n+j) (k:P i):P ρ:=by
 classical
 let S:=(L∪G.image (fun j=>n+j)).filter P
 have a (w:ℕ):w∈S↔(w∈L∨∃j∈G,w=n+j)∧P w:=by simp only[S,Finset.mem_filter,Finset.mem_union,Finset.mem_image,eq_comm]
 have l:S.Nonempty:=⟨i,(a i).2 ⟨r,k⟩⟩
 let m:=S.max' l
 have s:m∈S:=S.max'_mem l;obtain⟨c,f⟩:=(a m).1 s;by_cases g:m=ρ
 ·simpa[g] using f
 ·obtain⟨j,h,b⟩:=vO p c g;have o:n+j∈S:=(a (n+j)).2
   ⟨Or.inr ⟨j,h,rfl⟩,e j h m b f⟩
  exact False.elim ((not_lt_of_ge (S.le_max' _ o)) (d j (q j h) m b))
lemma tV (o:IsOrTree n C G L ρ)
  (c:ReadsBack n C) (p:∀j∈G,j<C.gates.length)
  (P:ℕ→Prop)
  (m:∀j∈G,P (n+j)↔∃i∈(gateAt C j).inputs,P i):
  ∀j∈G,P (n+j)→∃i∈L,P i∧i≤n+j:=by
 intro j
 induction j using Nat.strong_induction_on with
 | ind j ih=>
   intro d f;obtain⟨i,a,e⟩:=(m j d).1 f;have l:=c j (p j d) i a;rcases (o.1 j d).2.2 i a with q|⟨s,k⟩
   ·exact⟨i,q,e,l.le⟩
   ·have h:n+(i-n)=i:=by omega
    have b:P (n+(i-n)):=by rwa [h]
    obtain⟨w,r,g,t⟩:=ih (i-n) (by omega) k b;exact⟨w,r,g,by omega⟩
lemma fI (c:IsOrTree n C G L ρ)
  (b:ReadsBack n C) (k:∀j∈G,j<C.gates.length)
  (P:ℕ→Prop)
  (f:∀j∈G,P (n+j)↔∃i∈(gateAt C j).inputs,P i):
  P ρ↔∃i∈L,P i:=by
 constructor
 ·intro l;by_cases a:G= ∅
  ·have o:L={ρ}:=by simpa[a] using c.2.2.2
   exact⟨ρ,by simp[o],l⟩
  ·have e:∃j∈G,ρ=n+j:=by simpa[a] using c.2.2.2
   obtain⟨j,h,rfl⟩:=e;obtain⟨i,g,d,_⟩:=tV c b k P f j h l;exact⟨i,g,d⟩
 ·rintro⟨i,g,d⟩;exact pI c b k P
   (fun j h w p m=>(f j h).2 ⟨w,p,m⟩) (Or.inl g) d
def W {n:ℕ} (C:Circuit) (x:Fin n→Bool) (i:ℕ):Prop:=(C.wires (List.ofFn x)).getD i false=true
def aP (f:List Bool→Gate→Bool) (w:List Bool) (g:Gate):
  List Bool:=
 w++[f w g]
lemma kJ (f:List Bool→Gate→Bool) (gs:List Gate)
  (w:List Bool):(gs.foldl (aP f) w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil=>simp
 | cons g gs ih=>
   simp[ih,aP];omega
lemma dH (f:List Bool→Gate→Bool) (gs:List Gate)
  (w:List Bool) (i:ℕ) (a:i<w.length):
  (gs.foldl (aP f) w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
   rw[List.foldl_cons,ih _ (by simp[aP];omega)];exact List.getD_append _ _ _ _ a
lemma gB {n:ℕ} {C:Circuit} {j:ℕ}
  (f:List Bool→Gate→Bool) (v:List Bool) (h:v.length=n)
  (g:j<C.gates.length):
  ∃
   w:List Bool,w.length=n+j∧
   (C.gates.foldl (aP f) v).getD (n+j) false=f w (gateAt C j)∧
   ∀i<n+j,w.getD i false=(C.gates.foldl (aP f) v).getD i false:=by
 let w:=(C.gates.take j).foldl (aP f) v
 let b:=C.gates.drop (j+1)
 have c:C.gates=C.gates.take j++C.gates[j]::b:=
  (List.take_append_drop j C.gates).symm.trans
    (congrArg (C.gates.take j++ ·) (List.drop_eq_getElem_cons (l:=C.gates) g))
 have e:w.length=n+j:=by simp[w,kJ,h,Nat.min_eq_left g.le]
 have d:gateAt C j=C.gates[j]:=List.getD_eq_getElem _ _ g;have a:C.gates.foldl (aP f) v=
   b.foldl (aP f) (aP f w C.gates[j]):=by
  conv_lhs=>rw[c]
  rw[List.foldl_append,List.foldl_cons]
 refine⟨w,e,?_,?_⟩
 ·rw[a,dH f b (aP f w C.gates[j]) (n+j)
   (by simp[aP,e]),d]
  unfold aP;rw[List.getD_append_right _ _ _ _ (by omega),e,Nat.sub_self];rfl
 ·intro i k;rw[a,dH f b (aP f w C.gates[j]) i
   (by simp[aP,e];omega)]
  exact(List.getD_append w [f w C.gates[j]] false i (by omega)).symm
lemma aO {n:ℕ} {C:Circuit} {x:Fin n→Bool} {j:ℕ}
  (b:ReadsBack n C) (d:j<C.gates.length):
  (C.wires (List.ofFn x)).getD (n+j) false=
    (gateAt C j).op.eval ((gateAt C j).inputs.map
      fun i=>(C.wires (List.ofFn x)).getD i false):=by
 obtain⟨w,_,a,c⟩:=gB (n:=n) (fun w g=>g.op.eval (g.inputs.map fun i=>w.getD i false)) (List.ofFn x) (by simp) d;change(C.wires (List.ofFn x)).getD (n+j) false=(gateAt C j).op.eval ((gateAt C j).inputs.map fun i=>w.getD i false) at a;rw[a];congr 1;exact List.map_congr_left (fun i e=>c i (b j d i e))
lemma aY {n:ℕ} {C:Circuit} {x:Fin n→Bool} {j:ℕ}
  (a:ReadsBack n C) (c:j<C.gates.length) (b:(gateAt C j).op=GateOp.or):
  W C x (n+j)↔∃i∈(gateAt C j).inputs,W C x i:=by
 simp only[W,aO a c,b,GateOp.eval,List.any_map,Function.comp_def,id_eq,List.any_eq_true]
theorem gate_exists {j : ℕ} (h : (gateAt C j).inputs.length = 2) : j < C.gates.length := by
  by_contra hn
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hn)] at h

theorem original_output (x : Fin n → Bool) (tree : IsOrTree n C G L C.output)
    (back : ReadsBack n C) : C.eval (List.ofFn x) = true ↔ ∃ i ∈ L, W C x i := by
  have realGate (j : ℕ) (hj : j ∈ G) := gate_exists (tree.1 j hj).2.1
  exact fI tree back realGate (W C x) (fun j hj => aY back (realGate j hj) (tree.1 j hj).1)

theorem shared_term {x : Fin n → Bool} (back : ReadsBack n C) (j a b : ℕ)
    (op : (gateAt C j).op = GateOp.and)
    (args : (gateAt C j).inputs = [a,b] ∨ (gateAt C j).inputs = [b,a]) :
    W C x (n+j) ↔ W C x a ∧ W C x b := by
  have len : (gateAt C j).inputs.length = 2 := by rcases args with h|h <;> simp [h]
  unfold W
  rw [aO back (gate_exists len), op]
  rcases args with h | h <;> simp [h, GateOp.eval, and_comm]

theorem factored_original (x : Fin n → Bool) (tree : IsOrTree n C G L C.output)
    (back : ReadsBack n C) (i j a b c : ℕ) (hi : n+i ∈ L) (hj : n+j ∈ L)
    (opi : (gateAt C i).op = GateOp.and)
    (ai : (gateAt C i).inputs = [a,b] ∨ (gateAt C i).inputs = [b,a])
    (opj : (gateAt C j).op = GateOp.and)
    (aj : (gateAt C j).inputs = [a,c] ∨ (gateAt C j).inputs = [c,a]) :
    C.eval (List.ofFn x) = true ↔
      (W C x a ∧ (W C x b ∨ W C x c)) ∨ ∃ k ∈ (L.erase (n+i)).erase (n+j), W C x k := by
  rw [original_output x tree back]
  have leftTerm := shared_term (x := x) back i a b opi ai
  have rightTerm := shared_term (x := x) back j a c opj aj
  constructor
  · rintro ⟨k,hk,h⟩
    by_cases ei : k = n+i
    · subst k
      obtain ⟨ha,hb⟩ := leftTerm.mp h
      exact Or.inl ⟨ha, Or.inl hb⟩
    by_cases ej : k = n+j
    · subst k
      obtain ⟨ha,hc⟩ := rightTerm.mp h
      exact Or.inl ⟨ha,Or.inr hc⟩
    exact Or.inr ⟨k, Finset.mem_erase.mpr ⟨ej, Finset.mem_erase.mpr ⟨ei,hk⟩⟩,h⟩
  · rintro (⟨ha,hb|hc⟩ | ⟨k,hk,h⟩)
    · exact ⟨_, hi, leftTerm.mpr ⟨ha,hb⟩⟩
    · exact ⟨_, hj, rightTerm.mpr ⟨ha,hc⟩⟩
    · exact ⟨k,(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2,h⟩

end Original2775