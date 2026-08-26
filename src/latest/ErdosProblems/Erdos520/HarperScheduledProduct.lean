import ErdosProblems.Erdos520.HarperScheduledCDFStrong

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Scheduled finite-product Gaussian replacement

The summable one-block CDF estimates control every finite product rectangle.
The bound depends only on the first block index, not on the path length.
-/

/-- Every consecutive scheduled block product is uniformly close to the
matching independent Gaussian product on half-open coordinate rectangles. -/
theorem exists_eventually_harperScheduledProductRectangle_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          (∀ i : Fin n,
            HarperFejerSmoothedCDFIdentity
              (harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y
                  (start + (i : ℕ))) t t)
              (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y
                  (start + (i : ℕ))) t t)
              (harperScheduledComparisonFrequency
                (start + (i : ℕ)))) →
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
  obtain ⟨J, hJ⟩ :=
    exists_eventually_sum_harperScheduledDiagonalCDFDistance_le M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper hidentity a b hab
  let rho : Fin n → Measure ℝ := fun i ↦
    harperCenteredLinearBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t t
  let nu : Fin n → Measure ℝ := fun i ↦
    harperGaussianBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t t
  have hrectangle := abs_prod_measureReal_Ioc_sub_prod_le
    (Finset.univ : Finset (Fin n)) rho nu a b
    (fun i _hi ↦ hab i)
  have hsum :
      (∑ i : Fin n, 2 * harperCDFDistance (rho i) (nu i)) ≤
        520 / harperScheduledComparisonFrequency start := by
    have hsumNat := hJ start hstart n y hy t htLower htUpper
      (fun k hk ↦ hidentity ⟨k, Finset.mem_range.mp hk⟩)
    dsimp only [rho, nu]
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ ↦ 2 * harperCDFDistance
        (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y (start + k)) t t)
        (harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y (start + k)) t t)) n]
    exact hsumNat
  change |(∏ i : Fin n, (rho i).real (Ioc (a i) (b i))) -
      ∏ i : Fin n, (nu i).real (Ioc (a i) (b i))| ≤ _
  exact hrectangle.trans hsum

/-- Strong-frequency form of the product-rectangle comparison.  Its error is
`O(2^(-2^start))`, still independently of the number of coordinates. -/
theorem exists_eventually_harperScheduledProductRectangle_le_strong
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          (∀ i : Fin n,
            HarperFejerSmoothedCDFIdentity
              (harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y
                  (start + (i : ℕ))) t t)
              (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y
                  (start + (i : ℕ))) t t)
              (harperScheduledStrongComparisonFrequency
                (start + (i : ℕ)))) →
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
    exists_eventually_sum_harperScheduledDiagonalCDFDistance_le_strong M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper hidentity a b hab
  let rho : Fin n → Measure ℝ := fun i ↦
    harperCenteredLinearBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t t
  let nu : Fin n → Measure ℝ := fun i ↦
    harperGaussianBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t t
  have hrectangle := abs_prod_measureReal_Ioc_sub_prod_le
    (Finset.univ : Finset (Fin n)) rho nu a b
    (fun i _hi ↦ hab i)
  have hsum :
      (∑ i : Fin n, 2 * harperCDFDistance (rho i) (nu i)) ≤
        520 / harperScheduledStrongComparisonFrequency start := by
    have hsumNat := hJ start hstart n y hy t htLower htUpper
      (fun k hk ↦ hidentity ⟨k, Finset.mem_range.mp hk⟩)
    dsimp only [rho, nu]
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ ↦ 2 * harperCDFDistance
        (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y (start + k)) t t)
        (harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y (start + k)) t t)) n]
    exact hsumNat
  change |(∏ i : Fin n, (rho i).real (Ioc (a i) (b i))) -
      ∏ i : Fin n, (nu i).real (Ioc (a i) (b i))| ≤ _
  exact hrectangle.trans hsum

end Problem520
end Erdos
