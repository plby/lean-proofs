import ErdosProblems.Erdos520.HarperFejerInversion
import ErdosProblems.Erdos520.HarperScheduledProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Unconditional scheduled Gaussian replacement

The exact Fejér inversion theorem applies to the centered linear block and
its variance-matched Gaussian because both laws have a finite first moment.
This file discharges the last smoothing-identity hypotheses from the
ordinary- and strong-frequency scheduled CDF and product estimates.
-/

/-- Exact Fejér smoothing identity for an arbitrary centered linear prime
block and its variance-matched Gaussian comparison. -/
theorem harperCenteredLinearBlock_fejerSmoothedCDFIdentity
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ)
    {T : ℝ} (hT : 0 < T) :
    HarperFejerSmoothedCDFIdentity
      (harperCenteredLinearBlockLaw y S t u)
      (harperGaussianBlockLaw y S t u) T := by
  exact harperFejerSmoothedCDFIdentity_of_integrable_id
    (harperCenteredLinearBlockLaw y S t u)
    (harperGaussianBlockLaw y S t u)
    (integrable_id_harperCenteredLinearBlockLaw y S t u)
    (integrable_id_harperGaussianBlockLaw y S t u) hT

/-- Exact smoothing identity at the geometric comparison frequency
`T_j = 2^j`. -/
theorem harperScheduledFejerSmoothedCDFIdentity
    (y j : ℕ) (t u : ℝ) :
    HarperFejerSmoothedCDFIdentity
      (harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y j) t u)
      (harperGaussianBlockLaw y
        (harperScheduledPrimeBlock y j) t u)
      (harperScheduledComparisonFrequency j) := by
  exact harperCenteredLinearBlock_fejerSmoothedCDFIdentity
    y (harperScheduledPrimeBlock y j) t u
      (harperScheduledComparisonFrequency_pos j)

/-- Exact smoothing identity at the doubly-exponential comparison frequency
`T_j = 2^(2^j)`. -/
theorem harperScheduledStrongFejerSmoothedCDFIdentity
    (y j : ℕ) (t u : ℝ) :
    HarperFejerSmoothedCDFIdentity
      (harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y j) t u)
      (harperGaussianBlockLaw y
        (harperScheduledPrimeBlock y j) t u)
      (harperScheduledStrongComparisonFrequency j) := by
  exact harperCenteredLinearBlock_fejerSmoothedCDFIdentity
    y (harperScheduledPrimeBlock y j) t u
      (harperScheduledStrongComparisonFrequency_pos j)

/-- Unconditional geometric one-block Kolmogorov replacement rate. -/
theorem exists_eventually_harperScheduledDiagonalCDFDistance_le_geometric_unconditional
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          harperCDFDistance
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t)
            (harperGaussianBlockLaw y
              (harperScheduledPrimeBlock y j) t t) ≤
            130 / harperScheduledComparisonFrequency j := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledDiagonalCDFDistance_le_geometric M
  refine ⟨J, ?_⟩
  intro j hj y hy t htLower htUpper
  exact hJ j hj y hy t htLower htUpper
    (harperScheduledFejerSmoothedCDFIdentity y j t t)

/-- Unconditional doubly-exponential one-block Kolmogorov replacement rate. -/
theorem exists_eventually_harperScheduledDiagonalCDFDistance_le_strong_unconditional
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          harperCDFDistance
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t)
            (harperGaussianBlockLaw y
              (harperScheduledPrimeBlock y j) t t) ≤
            130 / harperScheduledStrongComparisonFrequency j := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledDiagonalCDFDistance_le_strong M
  refine ⟨J, ?_⟩
  intro j hj y hy t htLower htUpper
  exact hJ j hj y hy t htLower htUpper
    (harperScheduledStrongFejerSmoothedCDFIdentity y j t t)

/-- Unconditional local interval comparison: whenever the explicit strong
frequency error is dominated by the Gaussian cell mass, the scheduled block
assigns the cell at most twice that Gaussian mass. -/
theorem exists_eventually_harperScheduledIntervalProbability_le_two_mul_gaussian_unconditional
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ a delta : ℝ, 0 < delta → delta ≤ 1 →
            260 / harperScheduledStrongComparisonFrequency j ≤
              (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) →
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t).real
                (Ioc a (a + delta)) ≤
              2 * (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y j) t t).real
                  (Ioc a (a + delta)) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledIntervalProbability_le_two_mul_gaussian M
  refine ⟨J, ?_⟩
  intro j hj y hy t htLower htUpper
  exact hJ j hj y hy t htLower htUpper
    (harperScheduledStrongFejerSmoothedCDFIdentity y j t t)

/-- Unconditional total geometric CDF replacement budget for a consecutive
block path. -/
theorem exists_eventually_sum_harperScheduledDiagonalCDFDistance_le_unconditional
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          (∑ k ∈ Finset.range n,
            2 * harperCDFDistance
              (harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y (start + k)) t t)
              (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y (start + k)) t t)) ≤
            520 / harperScheduledComparisonFrequency start := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_sum_harperScheduledDiagonalCDFDistance_le M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper
  exact hJ start hstart n y hy t htLower htUpper
    (fun k _hk ↦
      harperScheduledFejerSmoothedCDFIdentity y (start + k) t t)

/-- Unconditional total strong-frequency CDF replacement budget for a
consecutive block path. -/
theorem exists_eventually_sum_harperScheduledDiagonalCDFDistance_le_strong_unconditional
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          (∑ k ∈ Finset.range n,
            2 * harperCDFDistance
              (harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y (start + k)) t t)
              (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y (start + k)) t t)) ≤
            520 / harperScheduledStrongComparisonFrequency start := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_sum_harperScheduledDiagonalCDFDistance_le_strong M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper
  exact hJ start hstart n y hy t htLower htUpper
    (fun k _hk ↦
      harperScheduledStrongFejerSmoothedCDFIdentity y (start + k) t t)

/-- Unconditional finite-product rectangle comparison at frequency `2^j`. -/
theorem exists_eventually_harperScheduledProductRectangle_le_unconditional
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ a b : Fin n → ℝ, (∀ i, a i ≤ b i) →
            |(∏ i : Fin n,
                (harperCenteredLinearBlockLaw y
                  (harperScheduledPrimeBlock y
                    (start + (i : ℕ))) t t).real
                    (Ioc (a i) (b i))) -
              ∏ i : Fin n,
                (harperGaussianBlockLaw y
                  (harperScheduledPrimeBlock y
                    (start + (i : ℕ))) t t).real
                    (Ioc (a i) (b i))| ≤
              520 / harperScheduledComparisonFrequency start := by
  obtain ⟨J, hJ⟩ := exists_eventually_harperScheduledProductRectangle_le M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper
  exact hJ start hstart n y hy t htLower htUpper
    (fun i ↦ harperScheduledFejerSmoothedCDFIdentity
      y (start + (i : ℕ)) t t)

/-- Unconditional finite-product rectangle comparison at the strong
frequency `2^(2^j)`. -/
theorem exists_eventually_harperScheduledProductRectangle_le_strong_unconditional
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ a b : Fin n → ℝ, (∀ i, a i ≤ b i) →
            |(∏ i : Fin n,
                (harperCenteredLinearBlockLaw y
                  (harperScheduledPrimeBlock y
                    (start + (i : ℕ))) t t).real
                    (Ioc (a i) (b i))) -
              ∏ i : Fin n,
                (harperGaussianBlockLaw y
                  (harperScheduledPrimeBlock y
                    (start + (i : ℕ))) t t).real
                    (Ioc (a i) (b i))| ≤
              520 / harperScheduledStrongComparisonFrequency start := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledProductRectangle_le_strong M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper
  exact hJ start hstart n y hy t htLower htUpper
    (fun i ↦ harperScheduledStrongFejerSmoothedCDFIdentity
      y (start + (i : ℕ)) t t)

end Problem520
end Erdos
