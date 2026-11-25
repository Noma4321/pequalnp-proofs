import PEqualNP.Outside.L_meta_1880

-- Adapted from the project's checked L_meta_1880, commit
-- 1eda360769e0b50a6d2b17bafd86f6035ee34c64, under Apache-2.0.
-- Its two-layer summary argument is extended here to any finite AND depth.
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
    (B : Finset (Sym2 (Fin n))) (R : Finset (Finset (Fin n))) : Prop :=
  ∀ u v : Fin n, s(u, v) ∉ B → fires C w (pairInput u v) →
    ∀ S : Finset (Fin n), S.card + width D * d ≤ contexts D → Apart (away G s(u, v)) {u, v} S →
      ∃ W ∈ R, Apart (away G s(u, v)) W S

def DepthSummary (D : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w d : ℕ)
    (B : Finset (Sym2 (Fin n))) (R : Finset (Finset (Fin n))) : Prop :=
  R.card ≤ (reps D) ∧ Facts G C w d R ∧ DepthCatches D G C w d B R

lemma depth_small_power {d : ℕ} (hd : d ≤ D) : 2 ^ d ≤ width D := Nat.pow_le_pow_right (by decide) (Nat.le_succ_of_le hd)

lemma depth_summary_mono {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {w d : ℕ}
    {B B' : Finset (Sym2 (Fin n))} {R : Finset (Finset (Fin n))}
    (h : DepthSummary D G C w d B R) (hsub : B ⊆ B') : DepthSummary D G C w d B' R :=
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
    (hf : Facts G C w d A) (ht : DepthCatches D G C w d B A) :
    ∃ R, DepthSummary D G C w d B R := by
  obtain ⟨R, hr, hb⟩ := representatives G h4 (width D) (contexts D) A (fun W hW => (hf W hW).1.trans (depth_small_power hd))
  refine ⟨R, hb, fun W hW => hf W (hr.1 hW), ?_⟩
  intro u v he hfire S hs hS
  obtain ⟨W, hW, hwS⟩ := ht u v he hfire S hs hS
  exact transfer_rep G (fun h => he (hc h)) hr hD (by omega) hW hwS

lemma depth_or_summary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q w dp dq d : ℕ} (hd : d ≤ D) (hp : dp ≤ d) (hq : dq ≤ d)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∨ fires C q x)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : DepthSummary D G C p dp B P) (hQ : DepthSummary D G C q dq B Q) :
    ∃ R, DepthSummary D G C w d (B ∪ charge G (vertices P ∪ vertices Q)) R := by
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
    rcases (sem _).mp hx with h | h
    · obtain ⟨W, hw, ha⟩ := hP.2.2 u v he' h S (by have := Nat.mul_le_mul_left (width D) hp; omega) hS
      exact ⟨W, Finset.mem_union_left _ hw, ha⟩
    · obtain ⟨W, hw, ha⟩ := hQ.2.2 u v he' h S (by have := Nat.mul_le_mul_left (width D) hq; omega) hS
      exact ⟨W, Finset.mem_union_right _ hw, ha⟩
  · intro W hW
    rcases Finset.mem_union.mp hW with h | h
    · exact (subset_vertices h).trans Finset.subset_union_left
    · exact (subset_vertices h).trans Finset.subset_union_right

lemma depth_and_summary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q w dp dq d : ℕ} (hd : d ≤ D) (hp : dp < d) (hq : dq < d)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∧ fires C q x)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : DepthSummary D G C p dp B P) (hQ : DepthSummary D G C q dq B Q) :
    ∃ R, DepthSummary D G C w d (B ∪ charge G (vertices P ∪ vertices Q)) R := by
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
    obtain ⟨hpf, hqf⟩ := (sem _).mp hx
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

lemma depth_stage_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q dp dq : ℕ} (hp : dp ≤ D) (hq : dq ≤ D)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : DepthSummary D G C p dp B P) (hQ : DepthSummary D G C q dq B Q) :
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

end VerifiedResults.Depth1735

