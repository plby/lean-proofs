import ErdosProblems.Erdos520.HarperCentralBandBarrier
import ErdosProblems.Erdos520.HarperTiltedLargeCoordinate

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal

namespace Erdos.Problem520

/-!
# Global Gaussian cell envelope on shrinking central bands

The central-band PNT gives the same variance window and moderate-cell local
limit theorem after shifting the first scheduled block by the band depth.
The variance-only large-coordinate estimate then supplies the missing cells,
with a summable variance-one Gaussian fallback and no additive tail error.
-/

/-- Every sufficiently shifted central-band tilted block cell is dominated
by the variance-matched Gaussian plus the summably weighted variance-one
fallback. -/
theorem
    exists_harperScheduledCentralBandGlobalCellProbability_le_gaussianMixture :
    ∃ J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ u : ℝ,
              |u - t| *
                  Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                    (1 / 64 : ℝ) →
                ∀ a : ℝ,
                  (harperCenteredLinearBlockLaw y
                      (harperScheduledPrimeBlock y j) t u).real
                        (Ioc a
                          (a + harperScheduledRelativeIntervalWidth j)) ≤
                    (1 + harperScheduledRelativeIntervalWidth j) *
                        (harperGaussianBlockLaw y
                          (harperScheduledPrimeBlock y j) t u).real
                            (Ioc a
                              (a +
                                harperScheduledRelativeIntervalWidth j)) +
                      harperScheduledRelativeIntervalWidth j *
                        (gaussianReal 0 (1 : ℝ≥0)).real
                          (Ioc a
                            (a + harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jmoderate, hJmoderate⟩ :=
    exists_harperScheduledCentralBandRelativeIntervalProbability_le_one_add_width_mul_gaussian
  obtain ⟨Jvar, hJvar⟩ :=
    exists_harperScheduledCentralBandOffDiagonalVariance_quarter_half
  obtain ⟨Jbudget, hJbudget⟩ := Filter.eventually_atTop.1
    eventually_scheduledOutsideCell_exponential_budget
  let J : ℕ := max (max Jmoderate Jvar) (max Jbudget 16)
  refine ⟨J, ?_⟩
  intro d j y hj hy t htLower htUpper u hscale a
  have hJj : J ≤ j := by omega
  have hjModerate : Jmoderate + d ≤ j := by
    dsimp [J] at hJj
    omega
  have hjVar : Jvar + d ≤ j := by
    dsimp [J] at hJj
    omega
  have hjBudget : Jbudget ≤ j := by
    dsimp [J] at hJj
    omega
  have hj16 : 16 ≤ j := by
    dsimp [J] at hJj
    omega
  by_cases ha : |a| + 1 ≤ (1 / 4 : ℝ) *
      Real.sqrt (((2 ^ j : ℕ) : ℝ))
  · have hmain := hJmoderate d j y hjModerate hy t
      htLower htUpper u hscale a ha
    exact hmain.trans (le_add_of_nonneg_right
      (mul_nonneg (harperScheduledRelativeIntervalWidth_pos j).le
        measureReal_nonneg))
  · have ha' : (1 / 4 : ℝ) *
        Real.sqrt (((2 ^ j : ℕ) : ℝ)) < |a| + 1 :=
      lt_of_not_ge ha
    have hvar := hJvar d j y hjVar hy t htLower htUpper u hscale
    have houtside :=
      harperScheduledOutsideCellProbability_le_width_mul_gaussianOne_of_variance
        hj16 t u a hvar.1 hvar.2 ha'
          (hJbudget j hjBudget a ha')
    exact houtside.trans (le_add_of_nonneg_left
      (mul_nonneg
        (by linarith [harperScheduledRelativeIntervalWidth_pos j] :
          0 ≤ 1 + harperScheduledRelativeIntervalWidth j)
        measureReal_nonneg))

end Erdos.Problem520
