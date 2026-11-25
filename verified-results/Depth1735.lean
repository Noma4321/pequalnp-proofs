import PEqualNP.Outside.L_meta_1880


-- Adapted from the project's checked L_meta_1880, commit
-- 1eda360769e0b50a6d2b17bafd86f6035ee34c64, under Apache-2.0.
-- Its two-layer summary argument is extended here to any finite AND depth.
-- The read-vector fold lemmas below are from the project proof L_meta_2230.
-- They are included here to keep the check independent of its blanket Mathlib import.
namespace VerifiedResults.ReadVectors1735
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

def FR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [FR S k R g]

lemma readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (stepR S k) ((List.range n).map (leafVectors S k)) := by
  rfl

lemma FR_or (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (h : g.op = GateOp.or) :
    FR S k R g =
      (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.or := h
  subst h2
  rfl

lemma FR_and (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (h : g.op = GateOp.and) :
    FR S k R g = (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.and := h
  subst h2
  rfl

lemma foldR_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepR]
    omega

lemma foldR_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ)
    (hi : i < R.length) : (gs.foldl (stepR S k) R).getD i [] = R.getD i [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepR S k R g).length := by simp [stepR]; omega
    rw [ih (stepR S k R g) hlt]
    simp [stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

lemma RV_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    RV C n S k w = leafVectors S k w := by
  simp only [RV]
  rw [readVectors_eq, foldR_getD_lt S k C.gates ((List.range n).map (leafVectors S k)) w
    (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma RV_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    ∃ Rp : List (List (List ℕ)),
      (∀ i, i < n + j → Rp.getD i [] = RV C n S k i) ∧
      RV C n S k (n + j) = FR S k Rp (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [gateAt_eq C j hj]; exact hgj
  rw [hga]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = pre.foldl (stepR S k) ((List.range n).map (leafVectors S k)) :=
    ⟨_, rfl⟩
  have hlen : Rp.length = n + j := by
    rw [hRp, foldR_length]
    simp only [List.length_map, List.length_range, hpre_len]
  have hall : readVectors C n S k = post.foldl (stepR S k) (stepR S k Rp gj) := by
    rw [readVectors_eq, hgs, List.foldl_append, List.foldl_cons, hRp]
  have hlen1 : (stepR S k Rp gj).length = n + j + 1 := by
    simp [stepR, hlen]
  refine ⟨Rp, ?_, ?_⟩
  · intro i hi
    simp only [RV]
    rw [hall, foldR_getD_lt S k post (stepR S k Rp gj) i (by omega)]
    simp [stepR, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < Rp.length by omega)]
  · simp only [RV]
    rw [hall, foldR_getD_lt S k post (stepR S k Rp gj) (n + j) (by omega)]
    simp [stepR, List.getD_eq_getElem?_getD, hlen]

lemma mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L.foldl insertNew acc) : v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => exact Or.inl h
  | cons x L ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · unfold insertNew at h1
      split_ifs at h1
      · exact Or.inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact Or.inl h2
        · have h3 : v = x := by simpa using h2
          exact Or.inr (by simp [h3])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma capAdd_pair (k x1 y1 x2 y2 : ℕ) :
    capAdd k [x1, y1] [x2, y2] = [min (x1 + x2) (k + 1), min (y1 + y2) (k + 1)] := by
  rfl


end VerifiedResults.ReadVectors1735

namespace VerifiedResults.Depth1735

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_1880

def width (D : ℕ) := 2 ^ (D + 1)
def contexts (D : ℕ) := width D * D
def reps (D : ℕ) := budget (width D) (contexts D)
def cost (D : ℕ) :=
  let v := 2 * (reps D * width D)
  v * (v + v * v)

def Layered {n : ℕ} (C : Circuit) (D : ℕ) (r : ℕ → ℕ) : Prop :=
  (∀ w, r w ≤ D) ∧
  ∀ j < C.gates.length, ∀ w ∈ (gateAt C j).inputs,
    r w ≤ r (n + j) ∧ ((gateAt C j).op = GateOp.and → r w < r (n + j))

private theorem room {D a b : ℕ} (h : a < b) :
    width D * a + width D ≤ width D * b := by
  simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (width D) (show a + 1 ≤ b from h)

variable {D : ℕ}

def DepthCatches (D : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w d : ℕ)
    (B : Finset (Sym2 (Fin n))) (R : Finset (Finset (Fin n)))
    (hit : Fin n → Fin n → Prop := fun u v => fires C w (pairInput u v)) : Prop :=
  ∀ u v : Fin n, s(u, v) ∉ B → hit u v →
    ∀ S : Finset (Fin n), S.card + width D * d ≤ contexts D → Apart (away G s(u, v)) {u, v} S →
      ∃ W ∈ R, Apart (away G s(u, v)) W S

def DepthSummary (D : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w d : ℕ)
    (B : Finset (Sym2 (Fin n))) (R : Finset (Finset (Fin n)))
    (hit : Fin n → Fin n → Prop := fun u v => fires C w (pairInput u v)) : Prop :=
  R.card ≤ (reps D) ∧ Facts G C w d R ∧ DepthCatches D G C w d B R hit

lemma depth_small_power {d : ℕ} (hd : d ≤ D) : 2 ^ d ≤ width D := Nat.pow_le_pow_right (by decide) (Nat.le_succ_of_le hd)

lemma depth_summary_mono {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {w d : ℕ}
    {B B' : Finset (Sym2 (Fin n))} {R : Finset (Finset (Fin n))}
    {hit : Fin n → Fin n → Prop} (h : DepthSummary D G C w d B R hit) (hsub : B ⊆ B') :
    DepthSummary D G C w d B' R hit :=
  ⟨h.1, h.2.1, fun u v he => h.2.2 u v (fun hin => he (hsub hin))⟩

lemma depth_input_summary {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (i : Fin n)
    (d : ℕ) (B : Finset (Sym2 (Fin n))) : DepthSummary D G C i d B {{i}} := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_singleton]
    unfold reps
    cases contexts D <;> simp [budget]
  · intro W hW
    obtain rfl := Finset.mem_singleton.mp hW
    refine ⟨by simpa using (Nat.one_le_pow d 2 (by decide)), ?_, ?_⟩
    · intro a ha b hb
      obtain rfl := Finset.mem_singleton.mp ha
      obtain rfl := Finset.mem_singleton.mp hb
      exact G.irrefl
    · intro x hx
      exact (fires_input ..).mpr (hx _ (Finset.mem_singleton_self _))
  · intro u v _ hx S _ hS
    obtain hu | hv := (pairInput_true ..).mp ((fires_input ..).mp hx)
    · exact ⟨{i}, by simp, fun a ha => hS a (by simp [Finset.mem_singleton.mp ha, hu])⟩
    · exact ⟨{i}, by simp, fun a ha => hS a (by simp [Finset.mem_singleton.mp ha, hv])⟩

lemma depth_compress {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {w d : ℕ} (hd : d ≤ D) {pool : Finset (Fin n)} {A : Finset (Finset (Fin n))}
    {B : Finset (Sym2 (Fin n))} (hD : ∀ W ∈ A, W ⊆ pool) (hc : charge G pool ⊆ B)
    {hit : Fin n → Fin n → Prop} (hf : Facts G C w d A) (ht : DepthCatches D G C w d B A hit) :
    ∃ R, DepthSummary D G C w d B R hit := by
  obtain ⟨R, hr, hb⟩ := representatives G h4 (width D) (contexts D) A (fun W hW => (hf W hW).1.trans (depth_small_power hd))
  refine ⟨R, hb, fun W hW => hf W (hr.1 hW), ?_⟩
  intro u v he hfire S hs hS
  obtain ⟨W, hW, hwS⟩ := ht u v he hfire S hs hS
  exact transfer_rep G (fun h => he (hc h)) hr hD (by omega) hW hwS

lemma depth_or_summary_for {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q w dp dq d : ℕ} (hd : d ≤ D) (hp : dp ≤ d) (hq : dq ≤ d)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∨ fires C q x)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    {pairP pairQ pairW : Fin n → Fin n → Prop}
    (split : ∀ u v, pairW u v → pairP u v ∨ pairQ u v)
    (hP : DepthSummary D G C p dp B P pairP) (hQ : DepthSummary D G C q dq B Q pairQ) :
    ∃ R, DepthSummary D G C w d (B ∪ charge G (vertices P ∪ vertices Q)) R pairW := by
  let pool := vertices P ∪ vertices Q
  apply depth_compress G h4 C hd (pool := pool) (A := P ∪ Q) _ (Finset.subset_union_right)
  · intro W hW
    rcases Finset.mem_union.mp hW with h | h
    · obtain ⟨hw, hi, hf⟩ := hP.2.1 W h
      exact ⟨hw.trans (Nat.pow_le_pow_right (by decide) hp), hi,
        fun x hx => (sem x).mpr (Or.inl (hf x hx))⟩
    · obtain ⟨hw, hi, hf⟩ := hQ.2.1 W h
      exact ⟨hw.trans (Nat.pow_le_pow_right (by decide) hq), hi,
        fun x hx => (sem x).mpr (Or.inr (hf x hx))⟩
  · intro u v he hx S hs hS
    have he' : s(u, v) ∉ B := fun h => he (Finset.mem_union_left _ h)
    rcases split u v hx with h | h
    · obtain ⟨W, hw, ha⟩ := hP.2.2 u v he' h S (by have := Nat.mul_le_mul_left (width D) hp; omega) hS
      exact ⟨W, Finset.mem_union_left _ hw, ha⟩
    · obtain ⟨W, hw, ha⟩ := hQ.2.2 u v he' h S (by have := Nat.mul_le_mul_left (width D) hq; omega) hS
      exact ⟨W, Finset.mem_union_right _ hw, ha⟩
  · intro W hW
    rcases Finset.mem_union.mp hW with h | h
    · exact (subset_vertices h).trans Finset.subset_union_left
    · exact (subset_vertices h).trans Finset.subset_union_right

lemma depth_or_summary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q w dp dq d : ℕ} (hd : d ≤ D) (hp : dp ≤ d) (hq : dq ≤ d)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∨ fires C q x)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : DepthSummary D G C p dp B P) (hQ : DepthSummary D G C q dq B Q) :
    ∃ R, DepthSummary D G C w d (B ∪ charge G (vertices P ∪ vertices Q)) R :=
  depth_or_summary_for G h4 C hd hp hq sem (fun u v => (sem (pairInput u v)).mp) hP hQ

lemma depth_and_summary_for {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q w dp dq d : ℕ} (hd : d ≤ D) (hp : dp < d) (hq : dq < d)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∧ fires C q x)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    {pairP pairQ pairW : Fin n → Fin n → Prop}
    (split : ∀ u v, pairW u v → pairP u v ∧ pairQ u v)
    (hP : DepthSummary D G C p dp B P pairP) (hQ : DepthSummary D G C q dq B Q pairQ) :
    ∃ R, DepthSummary D G C w d (B ∪ charge G (vertices P ∪ vertices Q)) R pairW := by
  classical
  let pool := vertices P ∪ vertices Q
  let raw := P.biUnion fun U => Q.image (fun V => U ∪ V)
  let A := raw.filter (fun W => Apart G.Adj W W)
  have memRaw (W : Finset (Fin n)) : W ∈ raw ↔ ∃ U ∈ P, ∃ V ∈ Q, U ∪ V = W := by
    simp only [raw, Finset.mem_biUnion, Finset.mem_image]
  have inD (U V : Finset (Fin n)) (hu : U ∈ P) (hv : V ∈ Q) : U ∪ V ⊆ pool :=
    Finset.union_subset_union (subset_vertices hu) (subset_vertices hv)
  have subD (W : Finset (Fin n)) (hw : W ∈ A) : W ⊆ pool := by
    obtain ⟨U, hu, V, hv, rfl⟩ := (memRaw W).mp (Finset.mem_filter.mp hw).1
    exact inD U V hu hv
  apply depth_compress G h4 C hd subD Finset.subset_union_right
  · intro W hW
    obtain ⟨hw, hi⟩ := Finset.mem_filter.mp hW
    obtain ⟨U, hu, V, hv, rfl⟩ := (memRaw W).mp hw
    obtain ⟨hsU, _, hfU⟩ := hP.2.1 U hu
    obtain ⟨hsV, _, hfV⟩ := hQ.2.1 V hv
    refine ⟨(Finset.card_union_le ..).trans ((Nat.add_le_add hsU hsV).trans (add_powers hp hq)),
      hi, ?_⟩
    intro x hx
    exact (sem x).mpr ⟨hfU x (fun z hz => hx z (Finset.mem_union_left _ hz)),
      hfV x (fun z hz => hx z (Finset.mem_union_right _ hz))⟩
  · intro u v he hx S hs hS
    let e := s(u, v)
    let E := away G e
    have heB : e ∉ B := fun h => he (Finset.mem_union_left _ h)
    have heD : e ∉ charge G pool := fun h => he (Finset.mem_union_right _ h)
    obtain ⟨hpf, hqf⟩ := split u v hx
    have hpairs : ({u, v} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    have hs₁ : (S ∪ {u, v}).card + width D * dp ≤ contexts D := by
      have hh := Finset.card_union_le S {u, v}
      have hstep := room (D := D) hp
      have ht : 2 ≤ width D := by unfold width; rw [pow_succ]; have := Nat.one_le_pow D 2 (by decide); omega
      omega
    obtain ⟨U, hu, huC⟩ := hP.2.2 u v heB hpf (S ∪ {u, v}) hs₁
      (apart_union_right.mpr ⟨hS, pair_apart G u v⟩)
    obtain ⟨huS, huPair⟩ := apart_union_right.mp huC
    have hpairU := apart_symm (away_symm (G := G) (e := e)) huPair
    obtain ⟨hsU, hiU, _⟩ := hP.2.1 U hu
    have hs₁' := hsU.trans (depth_small_power (D := D) (by omega))
    have hs₂ : (S ∪ U).card + width D * dq ≤ contexts D := by
      have hh := Finset.card_union_le S U
      have hstep := room (D := D) hq
      omega
    obtain ⟨V, hv, hvC⟩ := hQ.2.2 u v heB hqf (S ∪ U) hs₂
      (apart_union_right.mpr ⟨hS, hpairU⟩)
    obtain ⟨hvS, hvU⟩ := apart_union_right.mp hvC
    have huV := apart_symm (away_symm (G := G) (e := e)) hvU
    have hiV := (hQ.2.1 V hv).2.1
    have hi : Apart E (U ∪ V) (U ∪ V) :=
      apart_union_left.mpr ⟨apart_union_right.mpr ⟨apart_weaken hiU e, huV⟩,
        apart_union_right.mpr ⟨hvU, apart_weaken hiV e⟩⟩
    refine ⟨U ∪ V, Finset.mem_filter.mpr ⟨(memRaw _).mpr ⟨U, hu, V, hv, rfl⟩, ?_⟩,
      apart_union_left.mpr ⟨huS, hvS⟩⟩
    exact recover_independent G heD (inD U V hu hv) hi

lemma depth_and_summary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q w dp dq d : ℕ} (hd : d ≤ D) (hp : dp < d) (hq : dq < d)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∧ fires C q x)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : DepthSummary D G C p dp B P) (hQ : DepthSummary D G C q dq B Q) :
    ∃ R, DepthSummary D G C w d (B ∪ charge G (vertices P ∪ vertices Q)) R :=
  depth_and_summary_for G h4 C hd hp hq sem (fun u v => (sem (pairInput u v)).mp) hP hQ

lemma depth_stage_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q dp dq : ℕ} (hp : dp ≤ D) (hq : dq ≤ D)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    {pairP pairQ : Fin n → Fin n → Prop}
    (hP : DepthSummary D G C p dp B P pairP) (hQ : DepthSummary D G C q dq B Q pairQ) :
    (charge G (vertices P ∪ vertices Q)).card ≤ (cost D) := by
  apply charge_bound G h4 _ (2 * (reps D * width D))
  have sizeP := (vertices_bound P (width D) (fun W hW => (hP.2.1 W hW).1.trans (depth_small_power hp))).trans
    (Nat.mul_le_mul_right _ hP.1)
  have sizeQ := (vertices_bound Q (width D) (fun W hW => (hQ.2.1 W hW).1.trans (depth_small_power hq))).trans
    (Nat.mul_le_mul_right _ hQ.1)
  have h := Finset.card_union_le (vertices P) (vertices Q)
  omega

-- Go through the gates in order, retaining one common set of charged edges.
def Graded (n : ℕ) (C : Circuit) (r : ℕ → ℕ) : Prop :=
  ∀ j < C.gates.length, ∀ w ∈ (gateAt C j).inputs,
    r w ≤ r (n + j) ∧ ((gateAt C j).op = GateOp.and → r w < r (n + j))

lemma shallow_prefix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (r : ℕ → ℕ) (rankStep : Graded n C r)
    (k : ℕ) (hk : k ≤ C.gates.length) :
    ∃ B : Finset (Sym2 (Fin n)), B.card ≤ k * (cost D) ∧
      ∀ w < n + k, r w ≤ D → ∃ R, DepthSummary D G C w (r w) B R := by
  induction k with
  | zero =>
    refine ⟨∅, by simp, ?_⟩
    intro w hw _
    let i : Fin n := ⟨w, by omega⟩
    exact ⟨_, depth_input_summary G C i _ _⟩
  | succ j ih =>
    have hj : j < C.gates.length := by omega
    obtain ⟨B, hB, prev⟩ := ih (by omega)
    by_cases shallow : r (n + j) ≤ D
    · have hmem := gateAt_mem hj
      obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ hmem)
      have hpin : p ∈ (gateAt C j).inputs := by simp [hin]
      have hqin : q ∈ (gateAt C j).inputs := by simp [hin]
      have hp := hAO.2.1 j hj p hpin
      have hq := hAO.2.1 j hj q hqin
      have hpD := (rankStep j hj p hpin).1.trans shallow
      have hqD := (rankStep j hj q hqin).1.trans shallow
      obtain ⟨P, hP⟩ := prev p hp hpD
      obtain ⟨Q, hQ⟩ := prev q hq hqD
      let B' := B ∪ charge G (vertices P ∪ vertices Q)
      have step : ∃ R, DepthSummary D G C (n + j) (r (n + j)) B' R := by
        have sem := fires_gate C hj hin hp hq
        rcases hAO.1 _ hmem with ha | ho
        · exact depth_and_summary G h4 C shallow ((rankStep j hj p hpin).2 ha)
            ((rankStep j hj q hqin).2 ha) (fun x => (sem x).1 ha) hP hQ
        · exact depth_or_summary G h4 C shallow (rankStep j hj p hpin).1
            (rankStep j hj q hqin).1 (fun x => (sem x).2 ho) hP hQ
      refine ⟨B', ?_, ?_⟩
      · rw [Nat.succ_mul]
        exact (Finset.card_union_le ..).trans
          (Nat.add_le_add hB (depth_stage_cost G h4 C hpD hqD hP hQ))
      · intro w hw hd
        by_cases hold : w < n + j
        · obtain ⟨R, hr⟩ := prev w hold hd
          exact ⟨R, depth_summary_mono hr Finset.subset_union_left⟩
        · have he : w = n + j := by omega
          exact he ▸ step
    · refine ⟨B, hB.trans (Nat.mul_le_mul_right _ (by omega)), ?_⟩
      intro w hw hd
      have early : w < n + j := by
        by_contra bad
        have eq : w = n + j := by omega
        exact shallow (eq ▸ hd)
      exact prev w early hd


lemma depth_prefix_summaries {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (r : ℕ → ℕ) (layer : Layered (n := n) C D r)
    (k : ℕ) (hk : k ≤ C.gates.length) :
    ∃ B : Finset (Sym2 (Fin n)), B.card ≤ k * (cost D) ∧
      ∀ w < n + k, ∃ R, DepthSummary D G C w (r w) B R := by
  obtain ⟨B,hB,hAll⟩ := shallow_prefix (D := D) G h4 C hAO r layer.2 k hk
  exact ⟨B,hB,fun w hw => hAll w hw (layer.1 w)⟩

-- At the output an uncharged edge would produce an independent certificate
-- forcing the graph function. Turning on just those vertices contradicts it.
lemma depth_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (r : ℕ → ℕ) (layer : Layered (n := n) C D r) :
    G.edgeFinset.card ≤ C.size * (cost D) := by
  obtain ⟨B, hB, hAll⟩ := depth_prefix_summaries G h4 C hAO r layer C.gates.length le_rfl
  refine (Finset.card_le_card (show G.edgeFinset ⊆ B from ?_)).trans hB
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    by_contra hu
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have equiv (x : Fin n → Bool) : fires C C.output x ↔ graphFun G ∅ x = true := by
      change PEqualNP.MetaComplexity.circuitFun n C x = true ↔ _
      rw [hfun]
    have hfire := (equiv _).mpr ((graphFun_pair G u v).mpr hadj)
    have hlen : C.output < n + C.gates.length := by
      by_contra! h
      have hf := val_ge (C := C) (x := List.ofFn (pairInput u v)) (by simp) h
      exact Bool.noConfusion (hf.symm.trans hfire)
    obtain ⟨R, hr⟩ := hAll C.output hlen
    have hd := Nat.mul_le_mul_left (width D) (layer.1 C.output)
    obtain ⟨W, hW, _⟩ := hr.2.2 u v hu hfire ∅ (by simpa only [Finset.card_empty, zero_add, contexts] using hd) (by simp [Apart])
    obtain ⟨_, hi, force⟩ := hr.2.1 W hW
    let x (i : Fin n) := decide (i ∈ W)
    have yes := (equiv x).mp (force x (by simp [x]))
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, x] at yes
    obtain ⟨a, b, hab, ha, hb⟩ := yes
    exact hi a ha b hb hab


-- Count the union over all shallow wires that never fire on an independent input.
-- Deep gates elsewhere in the circuit impose no depth restriction on this result.
theorem shallow_wire_union {n D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (r : ℕ → ℕ)
    (rankStep : Graded n C r) (U : Finset (Sym2 (Fin n)))
    (hit : ∀ u v : Fin n, s(u, v) ∈ U → ∃ w < n + C.gates.length, r w ≤ D ∧
      fires C w (pairInput u v) ∧ (∀ x, fires C w x → graphFun G ∅ x = true)) :
    U.card ≤ C.size * cost D := by
  obtain ⟨B,hB,summaries⟩ := shallow_prefix (D := D) G h4 C hAO r rankStep C.gates.length le_rfl
  refine (Finset.card_le_card (show U ⊆ B from ?_)).trans hB
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    by_contra hu
    obtain ⟨w,hw,hd,hfire,sound⟩ := hit u v he
    obtain ⟨R,hr⟩ := summaries w hw hd
    have roomLeft := Nat.mul_le_mul_left (width D) hd
    obtain ⟨W,hW,_⟩ := hr.2.2 u v hu hfire ∅
      (by simpa only [Finset.card_empty,zero_add,contexts] using roomLeft) (by simp [Apart])
    obtain ⟨_,hi,force⟩ := hr.2.1 W hW
    let x (i : Fin n) := decide (i ∈ W)
    have yes := sound x (force x (by simp [x]))
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, x] at yes
    obtain ⟨a,b,hab,ha,hb⟩ := yes
    exact hi a ha b hb hab

-- OR chooses a true operand. AND must justify both operands, each with
-- one fewer AND layer available. The rest of the circuit can be arbitrarily deep.
def trace {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w d : ℕ) : Bool :=
  if h : w < n then x ⟨w,h⟩ else
    let g := gateAt C (w - n)
    match g.inputs with
    | [p,q] =>
      if _hp : p < w then
        if _hq : q < w then
          match g.op, d with
          | .or, k => trace C x p k || trace C x q k
          | .and, k+1 => trace C x p k && trace C x q k
          | _, _ => false
        else false
      else false
    | _ => false
termination_by w

private theorem trace_at_gate {n j p q d : ℕ} {C : Circuit} (x : Fin n → Bool)
    (hi : (gateAt C j).inputs = [p,q]) (hp : p < n+j) (hq : q < n+j) :
    trace C x (n+j) d = match (gateAt C j).op, d with
      | .or,k => trace C x p k || trace C x q k
      | .and,k+1 => trace C x p k && trace C x q k
      | _, _ => false := by
  rw [trace]
  simp [show ¬ n+j < n by omega, hi,hp,hq]

theorem trace_prefix {n D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (ao : IsAO2 n C) (k : ℕ) (hk : k ≤ C.gates.length) :
    ∃ B : Finset (Sym2 (Fin n)), B.card ≤ k * ((D+1) * cost D) ∧
      ∀ w < n+k, ∀ d ≤ D, ∃ R, DepthSummary D G C w d B R
        (fun u v => trace C (pairInput u v) w d = true) := by
  classical
  induction k with
  | zero =>
    refine ⟨∅,by simp,?_⟩
    intro w hw d _
    let i : Fin n := ⟨w,by omega⟩
    have h := depth_input_summary (D := D) G C i d ∅
    refine ⟨_,h.1,h.2.1,?_⟩
    intro u v he hit
    apply h.2.2 u v he
    apply (fires_input ..).mpr
    rw [trace] at hit
    simpa [i,show w < n by omega] using hit
  | succ j ih =>
    have hj : j < C.gates.length := by omega
    obtain ⟨B,hB,prev⟩ := ih (by omega)
    have mem := gateAt_mem hj
    obtain ⟨p,q,hi⟩ := List.length_eq_two.mp (ao.2.2 _ mem)
    have hp := ao.2.1 j hj p (by simp [hi])
    have hq := ao.2.1 j hj q (by simp [hi])
    have sem := fires_gate C hj hi hp hq
    have perLevel (d : Fin (D+1)) : ∃ (E : Finset (Sym2 (Fin n))) (R : Finset (Finset (Fin n))),
        E.card ≤ cost D ∧ DepthSummary D G C (n+j) d (B ∪ E) R
          (fun u v => trace C (pairInput u v) (n+j) d = true) := by
      have hd : d.val ≤ D := by omega
      rcases ao.1 _ mem with ha | ho
      · cases eq : d.val with
        | zero =>
          refine ⟨∅,∅,by simp,by simp,by simp [Facts],?_⟩
          intro u v _ hit
          simp [trace_at_gate _ hi hp hq,ha] at hit
        | succ m =>
          have hm : m ≤ D := by omega
          obtain ⟨P,hP⟩ := prev p hp m hm
          obtain ⟨Q,hQ⟩ := prev q hq m hm
          let E := charge G (vertices P ∪ vertices Q)
          have eBound := depth_stage_cost G h4 C hm hm hP hQ
          obtain ⟨R,hR⟩ := depth_and_summary_for G h4 C (by omega : m+1 ≤ D)
            (by omega : m < m+1) (by omega : m < m+1) (fun x => (sem x).1 ha)
            (pairW := fun u v => trace C (pairInput u v) (n+j) (m+1) = true)
            (fun u v h => by simpa [trace_at_gate _ hi hp hq,ha] using h) hP hQ
          exact ⟨E,R,eBound,hR⟩
      · obtain ⟨P,hP⟩ := prev p hp d hd
        obtain ⟨Q,hQ⟩ := prev q hq d hd
        have eBound := depth_stage_cost G h4 C hd hd hP hQ
        obtain ⟨R,hR⟩ := depth_or_summary_for G h4 C hd le_rfl le_rfl (fun x => (sem x).2 ho)
          (pairW := fun u v => trace C (pairInput u v) (n+j) d = true)
          (fun u v h => by simpa [trace_at_gate _ hi hp hq,ho] using h) hP hQ
        exact ⟨_,R,eBound,hR⟩
    choose E R eBound hR using perLevel
    let extra := Finset.univ.biUnion E
    have extraBound : extra.card ≤ (D+1)*cost D := by
      calc
        _ ≤ ∑ d, (E d).card := Finset.card_biUnion_le
        _ ≤ ∑ _d : Fin (D+1), cost D := Finset.sum_le_sum (fun d _ => eBound d)
        _ = _ := by simp
    refine ⟨B ∪ extra,?_,?_⟩
    · rw [Nat.succ_mul]
      exact (Finset.card_union_le ..).trans (Nat.add_le_add hB extraBound)
    · intro w hw d hd
      by_cases old : w < n+j
      · obtain ⟨T,hT⟩ := prev w old d hd
        exact ⟨T,depth_summary_mono hT Finset.subset_union_left⟩
      · have eq : w = n+j := by omega
        subst w
        let l : Fin (D+1) := ⟨d,by omega⟩
        exact ⟨R l,depth_summary_mono (hR l) (Finset.union_subset_union_right
          (Finset.subset_biUnion_of_mem E (Finset.mem_univ l)))⟩

-- Each counted edge may choose a different wire and a different certificate.
-- Only the successful OR branch counts toward the certificate's AND depth.
theorem trace_union {n D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (ao : IsAO2 n C) (U : Finset (Sym2 (Fin n)))
    (hit : ∀ u v : Fin n, s(u, v) ∈ U → ∃ w < n+C.gates.length, ∃ d ≤ D,
      trace C (pairInput u v) w d = true ∧
      (∀ x, fires C w x → graphFun G ∅ x = true)) :
    U.card ≤ C.size * ((D+1) * cost D) := by
  obtain ⟨B,hB,summaries⟩ := trace_prefix (D := D) G h4 C ao C.gates.length le_rfl
  refine (Finset.card_le_card (show U ⊆ B from ?_)).trans hB
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    by_contra hu
    obtain ⟨w,hw,d,hd,hitTrace,sound⟩ := hit u v he
    obtain ⟨R,hr⟩ := summaries w hw d hd
    have roomLeft := Nat.mul_le_mul_left (width D) hd
    obtain ⟨W,hW,_⟩ := hr.2.2 u v hu hitTrace ∅
      (by simpa only [Finset.card_empty,zero_add,contexts] using roomLeft) (by simp [Apart])
    obtain ⟨_,hi,force⟩ := hr.2.1 W hW
    let x (i : Fin n) := decide (i ∈ W)
    have yes := sound x (force x (by simp [x]))
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, x] at yes
    obtain ⟨a,b,hab,ha,hb⟩ := yes
    exact hi a ha b hb hab

-- With enough layers, a trace is exactly ordinary wire evaluation.
theorem trace_complete {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool)
    (k : ℕ) (hk : k ≤ C.gates.length) :
    ∀ w < n+k, ∀ d ≥ k, trace C x w d = true ↔ fires C w x := by
  induction k with
  | zero =>
    intro w hw d _
    have hw' : w < n := by omega
    let i : Fin n := ⟨w,hw'⟩
    rw [trace]
    simpa [hw',i] using (fires_input C i x).symm
  | succ j ih =>
    intro w hw d hd
    by_cases old : w < n+j
    · exact ih (by omega) w old d (by omega)
    · have eq : w = n+j := by omega
      subst w
      have hj : j < C.gates.length := by omega
      have mem := gateAt_mem hj
      obtain ⟨p,q,hi⟩ := List.length_eq_two.mp (ao.2.2 _ mem)
      have hp := ao.2.1 j hj p (by simp [hi])
      have hq := ao.2.1 j hj q (by simp [hi])
      have sem := fires_gate C hj hi hp hq x
      cases d with
      | zero => omega
      | succ m =>
        rcases ao.1 _ mem with ha | ho
        · rw [trace_at_gate _ hi hp hq, ha]
          simp only [Bool.and_eq_true,ih (by omega) p hp m (by omega),
            ih (by omega) q hq m (by omega)]
          exact (sem.1 ha).symm
        · rw [trace_at_gate _ hi hp hq, ho]
          simp only [Bool.or_eq_true,ih (by omega) p hp (m+1) (by omega),
            ih (by omega) q hq (m+1) (by omega)]
          exact (sem.2 ho).symm

def Covered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (D : ℕ) (e : Sym2 (Fin n)) : Prop :=
  ∀ u v : Fin n, e = s(u,v) → ∃ w < n+C.gates.length, ∃ d ≤ D,
    trace C (pairInput u v) w d = true ∧
    (∀ x, fires C w x → graphFun G ∅ x = true)

noncomputable def residual {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (D : ℕ) : Finset (Sym2 (Fin n)) := by
  classical
  exact (Ustar G C).filter (fun e => ¬ Covered G C D e)

theorem residual_bound {n D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (ao : IsAO2 n C) :
    (Ustar G C).card ≤ (residual G C D).card + C.size * ((D+1) * cost D) := by
  classical
  let S := (Ustar G C).filter (Covered G C D)
  have bound : S.card ≤ C.size * ((D+1)*cost D) :=
    trace_union G h4 C ao S (fun u v he => (Finset.mem_filter.mp he).2 u v rfl)
  have part := Finset.card_filter_add_card_filter_not (s := Ustar G C) (p := Covered G C D)
  change (Ustar G C).card ≤ ((Ustar G C).filter (fun e => ¬ Covered G C D e)).card + _
  dsimp [S] at bound
  omega

open PEqualNP.ReadK
open VerifiedResults.ReadVectors1735 (RV RV_input RV_gate FR_and FR_or mem_andStep
  capAdd_pair mem_foldl_insertNew readVectors_eq foldR_length)

-- In a bounded two-coordinate read vector neither coordinate has saturated.
-- Both children of an AND have a leaf, so each has strictly smaller total.
theorem vector_trace {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (a b : Fin n) (k w : ℕ) :
    ∀ v ∈ RV C n [a.val,b.val] k w, ∃ i j : ℕ, v = [i,j] ∧ 0 < i+j ∧
      (i ≤ k → j ≤ k → ∀ d, i+j ≤ d+1 → trace C (pairInput a b) w d = true) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    by_cases input : w < n
    · rw [RV_input _ _ _ _ _ input] at hv
      by_cases left : a.val = w
      · simp [leafVectors,left] at hv
        obtain rfl := hv
        refine ⟨_,_,rfl,by omega,?_⟩
        intro _ _ d _
        rw [trace,dite_eq_left input]
        exact (pairInput_true ..).mpr (Or.inl (Fin.ext left.symm))
      · by_cases right : b.val = w
        · simp [leafVectors,left,right] at hv
          obtain rfl := hv
          refine ⟨_,_,rfl,by omega,?_⟩
          intro _ _ d _
          rw [trace,dite_eq_left input]
          exact (pairInput_true ..).mpr (Or.inr (Fin.ext right.symm))
        · have no : w ∉ [a.val,b.val] := by simp [Ne.symm left, Ne.symm right]
          simp [leafVectors,no] at hv
    · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
      by_cases hj : j < C.gates.length
      · obtain ⟨p,q,hi⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hj))
        have hp := ao.2.1 j hj p (by simp [hi])
        have hq := ao.2.1 j hj q (by simp [hi])
        obtain ⟨pre,earlier,atGate⟩ := RV_gate C n [a.val,b.val] k j hj
        rcases ao.1 _ (gateAt_mem hj) with ha | ho
        · rw [atGate,FR_and _ _ _ _ ha,hi] at hv
          simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,earlier p hp,earlier q hq] at hv
          obtain ⟨t,ht,vq,hvq,rfl⟩ := mem_andStep _ _ _ _ hv
          obtain ⟨z,hz,vp,hvp,rfl⟩ := mem_andStep _ _ _ _ ht
          have hz' : z = [0,0] := by simpa using hz
          subst z
          obtain ⟨i₁,j₁,rfl,pos₁,sub₁⟩ := ih p hp vp hvp
          obtain ⟨i₂,j₂,rfl,pos₂,sub₂⟩ := ih q hq vq hvq
          rw [capAdd_pair,capAdd_pair]
          refine ⟨_,_,rfl,by omega,?_⟩
          intro ib jb d hd
          cases d with
          | zero => omega
          | succ m =>
            rw [trace_at_gate _ hi hp hq,ha]
            rw [Bool.and_eq_true]
            exact ⟨sub₁ (by omega) (by omega) m (by omega),
              sub₂ (by omega) (by omega) m (by omega)⟩
        · rw [atGate,FR_or _ _ _ _ ho,hi] at hv
          simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,earlier p hp,earlier q hq] at hv
          have either : v ∈ RV C n [a.val,b.val] k p ∨ v ∈ RV C n [a.val,b.val] k q := by
            rcases mem_foldl_insertNew _ _ _ hv with h | h
            · rcases mem_foldl_insertNew _ _ _ h with empty | h
              · simp at empty
              · exact Or.inl h
            · exact Or.inr h
          rcases either with h | h
          · obtain ⟨i,j',rfl,pos,sub⟩ := ih p hp v h
            refine ⟨i,j',rfl,pos,?_⟩
            intro hi' hj' d hd
            simp [trace_at_gate _ hi hp hq,ho,sub hi' hj' d hd]
          · obtain ⟨i,j',rfl,pos,sub⟩ := ih q hq v h
            refine ⟨i,j',rfl,pos,?_⟩
            intro hi' hj' d hd
            simp [trace_at_gate _ hi hp hq,ho,sub hi' hj' d hd]
      · have none : RV C n [a.val,b.val] k (n+j) = [] := by
          unfold RV
          rw [readVectors_eq]
          exact List.getD_eq_default _ _ (by rw [foldR_length]; simp; omega)
        simp [none] at hv

theorem read_pair_trace {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (a b : Fin n) (k : ℕ)
    (read : readsAtMost C n [a.val,b.val] k = true) :
    trace C (pairInput a b) C.output (2*k-1) = true := by
  obtain ⟨v,hv,hall⟩ := List.any_eq_true.mp read
  obtain ⟨i,j,rfl,_,proof⟩ := vector_trace C ao a b k C.output v hv
  simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq] at hall
  exact proof hall.1 hall.2 _ (by omega)

theorem read_edges_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (ao : IsAO2 n C)
    (computes : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (k : ℕ) (U : Finset (Sym2 (Fin n))) (edges : U ⊆ G.edgeFinset)
    (read : ∀ u v : Fin n, s(u,v) ∈ U → readsAtMost C n [u.val,v.val] k = true) :
    U.card ≤ C.size * ((2*k-1+1) * cost (2*k-1)) := by
  apply trace_union G h4 C ao
  intro u v he
  have equiv (x : Fin n → Bool) : fires C C.output x ↔ graphFun G ∅ x = true := by
    change PEqualNP.MetaComplexity.circuitFun n C x = true ↔ _
    rw [computes]
  have actual := (equiv _).mpr ((graphFun_pair G u v).mpr (SimpleGraph.mem_edgeFinset.mp (edges he)))
  have hw : C.output < n+C.gates.length := by
    by_contra! h
    have hf := val_ge (C := C) (x := List.ofFn (pairInput u v)) (by simp) h
    exact Bool.noConfusion (hf.symm.trans actual)
  exact ⟨C.output,hw,2*k-1,le_rfl,read_pair_trace C ao u v k (read u v he),fun x => (equiv x).mp⟩

-- Residual in terms of the project's readVectors alone. An unordered edge
-- passes the bounded-read test if it passes in both enumerations.
noncomputable def hardReads {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : ℕ) : Finset (Sym2 (Fin n)) := by
  classical
  exact (Ustar G C).filter (fun e => ¬ ∀ a b : Fin n, s(a,b) = e →
    readsAtMost C n [a.val,b.val] k = true)

theorem read_remainder {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (least : IsLeastAO G C) (k : ℕ) :
    (Ustar G C).card ≤ (hardReads G C k).card + C.size * ((2*k-1+1) * cost (2*k-1)) := by
  classical
  let good (e : Sym2 (Fin n)) := ∀ a b : Fin n, s(a,b) = e → readsAtMost C n [a.val,b.val] k = true
  let U := (Ustar G C).filter good
  have edges : U ⊆ G.edgeFinset := (Finset.filter_subset ..).trans Finset.sdiff_subset
  have bound := read_edges_bound G h4 C least.1 least.2.1 k U edges
    (fun a b he => (Finset.mem_filter.mp he).2 a b rfl)
  have part := Finset.card_filter_add_card_filter_not (s := Ustar G C) (p := good)
  change (Ustar G C).card ≤ ((Ustar G C).filter (fun e => ¬ good e)).card + _
  dsimp only [U] at bound
  omega

-- The quantified conclusion is the desk's L-meta-1735. A single k suffices.
theorem suffices_hard_reads (k : ℕ)
    (hard : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ u : Fin n, ∀ p : G.Walk u u, p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → (hardReads G C k).card ≤ c * (C.size+1)) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ u : Fin n, ∀ p : G.Walk u u, p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → (Ustar G C).card ≤ c * (C.size+1) := by
  obtain ⟨c,hc⟩ := hard
  let t := (2*k-1+1) * cost (2*k-1)
  refine ⟨c+t,?_⟩
  intro n G _ girth edge C least top
  have h4 : NoFourCycle G := by
    intro a b hab
    by_contra! h
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp h
    obtain ⟨_,hau,hbu⟩ := Finset.mem_filter.mp hu
    obtain ⟨_,hav,hbv⟩ := Finset.mem_filter.mp hv
    exact no4 G girth a u b v hau hbu.symm hbv hav.symm hab huv
  have short : C.size*t ≤ t*(C.size+1) := by rw [Nat.mul_comm C.size]; exact Nat.mul_le_mul_left _ (by omega)
  exact (read_remainder G h4 C least k).trans
    ((Nat.add_le_add (hc n G girth edge C least top) short).trans (Nat.add_mul ..).symm.le)

end VerifiedResults.Depth1735

