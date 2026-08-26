import ErdosProblems.Erdos745.EdgeLaw

/-! # Finite union bounds for the exact graph law -/

open scoped BigOperators

namespace Erdos745

noncomputable section

theorem probability_or_le (lam : ℝ) (n : ℕ) (P Q : SimpleGraph (Fin n) → Prop) :
    probability lam n (fun G ↦ P G ∨ Q G) ≤ probability lam n P + probability lam n Q := by
  simp only [probability_eq_edgeEventMass]
  exact Erdos746.BernoulliFinset.eventMass_or_le _ (edgeProbability lam n).property.1
    (edgeProbability lam n).property.2 _ _

theorem probability_exists_finset_le {ι : Type*} (lam : ℝ) (n : ℕ)
    (I : Finset ι) (P : ι → SimpleGraph (Fin n) → Prop) :
    probability lam n (fun G ↦ ∃ i ∈ I, P i G) ≤ ∑ i ∈ I, probability lam n (P i) := by
  classical
  induction I using Finset.induction with
  | empty => simp
  | @insert i I hi ih =>
    simp only [Finset.exists_mem_insert, Finset.sum_insert hi]
    exact (probability_or_le lam n _ _).trans (add_le_add le_rfl ih)

theorem probability_exists_le {ι : Type*} [Fintype ι] (lam : ℝ) (n : ℕ)
    (P : ι → SimpleGraph (Fin n) → Prop) :
    probability lam n (fun G ↦ ∃ i, P i G) ≤ ∑ i, probability lam n (P i) := by
  simpa using probability_exists_finset_le lam n Finset.univ P

end

end Erdos745
