import ErdosProblems.Erdos906.BorelCantelli
import ErdosProblems.Erdos906.Topology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ENNReal

namespace CofiniteDerivatives

variable {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]

/-- The event that the `n`-th random set misses the `j`-th basic open set. -/
def holeEvent (Z : Ω → ℕ → Set X) (B : ℕ → Set X) (j n : ℕ) : Set Ω :=
  {ω | ¬(Z ω n ∩ B j).Nonempty}

/-- Summable hole probabilities on a countable inner base produce one deterministic sample whose
sets hit every nonempty open set cofinitely often. This is the complete probabilistic-to-topological
interface; it uses no independence assumptions. -/
theorem exists_cofinitelyHits_of_summable_holes
    (μ : Measure Ω) [NeZero μ]
    (Z : Ω → ℕ → Set X) (B : ℕ → Set X)
    (hB : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ j, B j ⊆ U)
    (hsum : ∀ j, (∑' n, μ (holeEvent Z B j n)) ≠ ∞) :
    ∃ ω, CofinitelyHits (Z ω) := by
  classical
  obtain ⟨ω, hω⟩ := exists_forall_eventually_not_failure μ (holeEvent Z B) hsum
  refine ⟨ω, fun U hU hUne ↦ ?_⟩
  obtain ⟨j, hjU⟩ := hB U hU hUne
  obtain ⟨N, hN⟩ := hω j
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnotHole := hN n hn
  simp only [holeEvent, mem_ofPred_eq, not_not] at hnotHole
  rcases hnotHole with ⟨z, hzZ, hzB⟩
  exact ⟨z, hzZ, hjU hzB⟩

/-- The same extraction, immediately converted to density along every increasing subsequence. -/
theorem exists_everySubsequenceDense_of_summable_holes
    (μ : Measure Ω) [NeZero μ]
    (Z : Ω → ℕ → Set X) (B : ℕ → Set X)
    (hB : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ j, B j ⊆ U)
    (hsum : ∀ j, (∑' n, μ (holeEvent Z B j n)) ≠ ∞) :
    ∃ ω, EverySubsequenceDense (Z ω) := by
  obtain ⟨ω, hω⟩ := exists_cofinitelyHits_of_summable_holes μ Z B hB hsum
  exact ⟨ω, (cofiniteHits_iff_everySubsequenceDense (Z ω)).mp hω⟩

end CofiniteDerivatives
