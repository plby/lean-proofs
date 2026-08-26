import ErdosProblems.Erdos1002.GaussPrefixLateAggregateCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary bounds for the late prefix--future means

These bounds keep the factorized main term honest: a future block is an
indicator under the probability Gauss measure, so its complex expectation
has norm at most one.
-/

open MeasureTheory Set

namespace Erdos1002

noncomputable section

/-- The expectation of every finite future digit block has norm at most
one.  No independence hypothesis is involved. -/
theorem norm_gaussLateFutureDigitBlockMean_le_one
    {r : ℕ} (base : ℕ) (times : Fin r → ℕ)
    (events : Fin r → Set ℝ) :
    ‖gaussLateFutureDigitBlockMean base times events‖ ≤ 1 := by
  unfold gaussLateFutureDigitBlockMean
  calc
    ‖∫ x, gaussFutureDigitBlockIndicator base times events x
        ∂gaussMeasure‖ ≤
        ∫ _x : ℝ, (1 : ℝ) ∂gaussMeasure := by
      apply norm_integral_le_of_norm_le (integrable_const 1)
      filter_upwards with x
      unfold gaussFutureDigitBlockIndicator
      by_cases hx :
          x ∈ (gaussOrbit base) ⁻¹'
            shiftedGaussTailEvent base times events
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    _ = 1 := by simp

end

end Erdos1002
