import ErdosProblems.Erdos489.FiniteForbiddenConvergence
import ErdosProblems.Erdos489.ProblemDefinitions

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
A faithful positive-answer formalization of Erdős Problem 489.

The original display presupposes that the sifted set can be enumerated as an
infinite increasing sequence. This is represented by the explicit hypothesis
`(sievedSet A).Infinite`.
-/

namespace Erdos489

open Classical Filter
open scoped Topology BigOperators

/-- A positive answer to Erdős Problem 489. -/
theorem erdos489_statement :
    ∀ A : Set ℕ,
      (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ))
          =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ)) →
      (sievedSet A).Infinite →
      ∃ L : ℝ,
        Tendsto (fun x : ℕ => gapSumSq A x / (x : ℝ)) atTop (𝓝 L) := by
  intro A hthin hB
  by_cases hAinf : A.Infinite
  · exact exists_original_limit_of_infinite_forbidden A hAinf hthin hB
  · rw [Set.not_infinite] at hAinf
    exact exists_original_limit_of_finite_forbidden A hAinf hB

end Erdos489
