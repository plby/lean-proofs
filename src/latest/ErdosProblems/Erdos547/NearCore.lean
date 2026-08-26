import ErdosProblems.Erdos547.ManyNonleaves
import ErdosProblems.Erdos547.FewNonleaves

/-!
# The complete sufficiently-large near-core Ramsey proposition
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

open scoped Classical in
/-- Every sufficiently large two-coloured complete graph with a monochromatic
near-core contains a monochromatic copy of every tree of the required order. -/
theorem eventually_ramsey_of_near_core :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (T : SimpleGraph (Fin (m + 1)))
      (R : SimpleGraph (Fin (2 * m))) (A : Finset (Fin (2 * m))),
      T.IsTree → A.Nonempty →
      (∀ v ∈ A, (1 - 1 / coreDeficitDivisor : ℝ) * m ≤ degreeIn R A v) →
      T ⊑ R ∨ T ⊑ Rᶜ := by
  classical
  obtain ⟨m₁, hm₁⟩ := eventually_ramsey_of_near_core_many_nonleaves
  refine ⟨max coreDeficitDivisor m₁, ?_⟩
  intro m hm T R A hT hA hdegree
  have hmD : coreDeficitDivisor ≤ m := (le_max_left _ _).trans hm
  have hm₁' : m₁ ≤ m := (le_max_right _ _).trans hm
  by_cases hcore : Fintype.card (treeCore T) < m / (4 * corePairDivisor)
  · exact ramsey_of_near_core_few_nonleaves hmD T hT R A hA hdegree hcore
  · exact hm₁ m hm₁' T R A hT hA hdegree (le_of_not_gt hcore)

end Erdos547

#print axioms Erdos547.eventually_ramsey_of_near_core
