namespace VerifiedResults.Mutual5012

universe u
variable {X : Type u}

-- Each predicate denotes the assignments that make a wire true.
def Safe (F A : X → Prop) := ∀ x, A x → F x

theorem cross_conditions (F S T G H : X → Prop) :
    Safe F (fun x => (S x ∨ G x) ∧ (T x ∨ H x)) ↔
    Safe F (fun x => S x ∧ T x) ∧ Safe F (fun x => S x ∧ H x) ∧
    Safe F (fun x => G x ∧ T x) ∧ Safe F (fun x => G x ∧ H x) := by
  constructor
  · intro h
    exact ⟨fun x p => h x ⟨Or.inl p.1, Or.inl p.2⟩,
      fun x p => h x ⟨Or.inl p.1, Or.inr p.2⟩,
      fun x p => h x ⟨Or.inr p.1, Or.inl p.2⟩,
      fun x p => h x ⟨Or.inr p.1, Or.inr p.2⟩⟩
  · rintro ⟨a, b, c, d⟩ x ⟨hs | hg, ht | hh⟩
    · exact a x ⟨hs, ht⟩
    · exact b x ⟨hs, hh⟩
    · exact c x ⟨hg, ht⟩
    · exact d x ⟨hg, hh⟩

-- Two unsafe operands of a safe top require distinct false-output witnesses.
theorem distinct_witnesses (F S T G H : X → Prop)
    (top : Safe F (fun x => (S x ∨ G x) ∧ (T x ∨ H x)))
    (left : ¬ Safe F G) (right : ¬ Safe F H) :
    ∃ x y, x ≠ y ∧ ¬ F x ∧ G x ∧ ¬ T x ∧ ¬ H x ∧
      ¬ F y ∧ H y ∧ ¬ S y ∧ ¬ G y := by
  classical
  have witness (A : X → Prop) (bad : ¬ Safe F A) : ∃ x, A x ∧ ¬ F x := by
    apply Classical.byContradiction
    intro none
    apply bad
    intro x ha
    exact Classical.byContradiction (fun hn => none ⟨x, ha, hn⟩)
  obtain ⟨x, gx, nx⟩ := witness G left
  obtain ⟨y, hy, ny⟩ := witness H right
  have killX : ¬ (T x ∨ H x) := fun h => nx (top x ⟨Or.inr gx, h⟩)
  have killY : ¬ (S y ∨ G y) := fun h => ny (top y ⟨h, Or.inr hy⟩)
  exact ⟨x, y, fun e => killY (Or.inr (e ▸ gx)), nx, gx,
    fun h => killX (Or.inl h), fun h => killX (Or.inr h), ny, hy,
    fun h => killY (Or.inl h), fun h => killY (Or.inr h)⟩

end VerifiedResults.Mutual5012
