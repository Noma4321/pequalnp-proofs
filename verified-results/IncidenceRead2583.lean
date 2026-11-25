import PEqualNP.Defs.ReadK

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

namespace VerifiedResults.IncidenceRead

theorem read_of_edges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (k : ℕ)
    (computes : ∀ z, circuitFun (N + N) C z = decide
      (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (edge : ∀ p l, I p l → readsAtMost C (N + N)
      (setList {Fin.castAdd N p, Fin.natAdd N l}) k = true) :
    IsReadK (N + N) C k := by
  intro S prime
  obtain ⟨onS, minimal⟩ := prime
  rw [computes] at onS
  obtain ⟨p, l, inc, hp, hl⟩ := of_decide_eq_true onS
  let E : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l}
  have subset : E ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact h ▸ of_decide_eq_true hp
    · exact (Finset.mem_singleton.mp h) ▸ of_decide_eq_true hl
  have eq : E = S := by
    by_contra ne
    have off := minimal E (Finset.mem_ssubsets.mpr (ssubset_of_subset_of_ne subset ne))
    have onE : circuitFun (N + N) C (setInput E) = true := by
      rw [computes]
      apply decide_eq_true
      exact ⟨p, l, inc, by simp [setInput, E], by simp [setInput, E]⟩
    simp [onE] at off
  rw [← eq]
  exact edge p l inc

end VerifiedResults.IncidenceRead
