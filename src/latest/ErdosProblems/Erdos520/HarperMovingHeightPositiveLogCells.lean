import ErdosProblems.Erdos520.HarperMovingHeightMoments
import ErdosProblems.Erdos520.HarperVarianceExplicitBarrier
import ErdosProblems.Erdos520.HarperTiltedLargeCoordinate

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal

namespace Erdos.Problem520

/-!
# Uniform Gaussian cells on growing noncentral height windows

The strong-PNT arithmetic puts every scheduled off-diagonal variance in
`(1/4, 1/2)` after one absolute cutoff plus the explicit shift
`clog 2 (M + 1)`.  The variance-explicit CDF and relative-cell estimates are
then completely uniform in the height cutoff `M`.  Combining the moderate
relative estimate with the variance-one large-cell fallback gives the global
Gaussian-mixture cell envelope with the same single shifted cutoff.
-/

/-- Moving-height specialization of the variance-explicit strong CDF
comparison.  The cutoff is absolute; all dependence on the height window is
recorded by the explicit logarithmic shift. -/
theorem exists_harperScheduledMovingHeightCDFDistance_le_strong :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
            |u - t| *
                Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                  (1 / 64 : ℝ) →
              harperCDFDistance
                  (harperCenteredLinearBlockLaw y
                    (harperScheduledPrimeBlock y j) t u)
                  (harperGaussianBlockLaw y
                    (harperScheduledPrimeBlock y j) t u) ≤
                130 / harperScheduledStrongComparisonFrequency j := by
  obtain ⟨J, hJ⟩ :=
    exists_harperScheduledMovingHeightOffDiagonalVariance_quarter_half
  refine ⟨J, ?_⟩
  intro M j y hj hy t htLower htUpper u hscale
  exact harperScheduledOffDiagonalCDFDistance_le_strong_of_variance_quarter
    (hJ M j y hj hy t htLower htUpper u hscale).1

/-- Uniform moving-height relative local limit estimate on every scheduled
moderate cell. -/
theorem
    exists_harperScheduledMovingHeightRelativeIntervalProbability_le_one_add_width_mul_gaussian :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
            |u - t| *
                Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                  (1 / 64 : ℝ) →
              ∀ a : ℝ,
                |a| + 1 ≤ (1 / 4 : ℝ) *
                  Real.sqrt (((2 ^ j : ℕ) : ℝ)) →
                (harperCenteredLinearBlockLaw y
                    (harperScheduledPrimeBlock y j) t u).real
                      (Ioc a
                        (a + harperScheduledRelativeIntervalWidth j)) ≤
                  (1 + harperScheduledRelativeIntervalWidth j) *
                    (harperGaussianBlockLaw y
                      (harperScheduledPrimeBlock y j) t u).real
                        (Ioc a
                          (a + harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jvar, hJvar⟩ :=
    exists_harperScheduledMovingHeightOffDiagonalVariance_quarter_half
  obtain ⟨Jcell, hJcell⟩ := Filter.eventually_atTop.1
    eventually_harperScheduledOffDiagonalRelativeIntervalProbability_le_one_add_width_mul_gaussian_of_variance
  refine ⟨max Jvar Jcell, ?_⟩
  intro M j y hj hy t htLower htUpper u hscale a ha
  have hvar := hJvar M j y (by omega) hy t htLower htUpper u hscale
  exact hJcell j (by omega) y t u a hvar.1 hvar.2 ha

/-- Every coordinate variance in a moving-height scheduled path lies in the
uniform Gaussian window after the same single shifted cutoff. -/
theorem exists_harperScheduledMovingHeightVarianceVector_quarter_half :
    ∃ J : ℕ, ∀ M start n y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
            (∀ i : Fin n,
              |u i - t| *
                  Real.log (harperBlockEndpoint
                    (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
              ∀ i : Fin n,
                (1 / 4 : ℝ) <
                    harperLinearBlockVariance y
                      (harperScheduledPrimeBlock y
                        (start + (i : ℕ))) t (u i) ∧
                  harperLinearBlockVariance y
                    (harperScheduledPrimeBlock y
                      (start + (i : ℕ))) t (u i) < (1 / 2 : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_harperScheduledMovingHeightOffDiagonalVariance_quarter_half
  refine ⟨J, ?_⟩
  intro M start n y hstart hy t htLower htUpper u hscale i
  have hindex : J + Nat.clog 2 (M + 1) ≤ start + (i : ℕ) := by
    omega
  have hendpoint :
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  exact hJ M (start + (i : ℕ)) y hindex hendpoint
    t htLower htUpper (u i) (hscale i)

/-- Global moving-height cell envelope.  The variance-matched Gaussian
controls the moderate region, while the summably weighted variance-one
Gaussian controls every remaining cell.  One fixed `J` works for all height
cutoffs after the explicit `clog` shift. -/
theorem
    exists_harperScheduledMovingHeightGlobalCellProbability_le_gaussianMixture :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
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
                            (a + harperScheduledRelativeIntervalWidth j)) +
                    harperScheduledRelativeIntervalWidth j *
                      (gaussianReal 0 (1 : ℝ≥0)).real
                        (Ioc a
                          (a + harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jmoderate, hJmoderate⟩ :=
    exists_harperScheduledMovingHeightRelativeIntervalProbability_le_one_add_width_mul_gaussian
  obtain ⟨Jvar, hJvar⟩ :=
    exists_harperScheduledMovingHeightOffDiagonalVariance_quarter_half
  obtain ⟨Jbudget, hJbudget⟩ := Filter.eventually_atTop.1
    eventually_scheduledOutsideCell_exponential_budget
  let J : ℕ := max (max Jmoderate Jvar) (max Jbudget 16)
  refine ⟨J, ?_⟩
  intro M j y hj hy t htLower htUpper u hscale a
  have hJj : J ≤ j := by omega
  have hjModerate :
      Jmoderate + Nat.clog 2 (M + 1) ≤ j := by
    dsimp [J] at hJj
    omega
  have hjVar : Jvar + Nat.clog 2 (M + 1) ≤ j := by
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
  · have hmain := hJmoderate M j y hjModerate hy t
      htLower htUpper u hscale a ha
    exact hmain.trans (le_add_of_nonneg_right
      (mul_nonneg (harperScheduledRelativeIntervalWidth_pos j).le
        measureReal_nonneg))
  · have ha' : (1 / 4 : ℝ) *
        Real.sqrt (((2 ^ j : ℕ) : ℝ)) < |a| + 1 :=
      lt_of_not_ge ha
    have hvar := hJvar M j y hjVar hy t htLower htUpper u hscale
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
