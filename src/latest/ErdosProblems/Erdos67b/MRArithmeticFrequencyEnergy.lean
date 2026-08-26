import ErdosProblems.Erdos67b.MRNarrowPrimePartition

/-!
# Frequency energy for the actual arithmetic subblocks

The supports and coefficients are now the ones in the finite typical
Ramaré decomposition. All rectangle, prime-band, and coefficient
hypotheses of the class estimates are discharged here.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

/-- Every higher first-small class has the summable product energy for
the actual labelled prime sets and typical cofactor rectangles. -/
theorem mrArithmetic_firstSmallClass_product_energy_le
    (blocks : Finset (ℕ × ℕ))
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) {T : ℝ} (hT : 0 ≤ T) :
    mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j *
      (∑ r ∈ mrScheduledSubblocks eta p₁ q₁ j, ∫ t in -T..T,
        (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) j).indicator
          (fun t ↦ ‖logarithmicDirichletPolynomial (mrScheduledPrimeSubblock eta p₁ q₁ j r)
              (mrFinitePrimeLineCoefficient f) t *
            logarithmicDirichletPolynomial (mrScheduledTypicalCofactor blocks eta p₁ q₁ j r X)
              (mrFiniteCofactorLineCoefficient (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f) t‖ ^ 2) t) ≤
      512 * Real.exp 13 * (1 + Real.pi) * (T / X + 1) /
        ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1))) := by
  have hlogq : 1 ≤ Real.log q₁ := by
    have hh := Real.log_le_log (Real.exp_pos 1) hqexp
    rwa [Real.log_exp] at hh
  have hHcur := mrLogSchedule_resolution_four_le heta1 (by linarith : 0 ≤ p₁) hlogq hbudget
    (show 1 ≤ j by omega)
  have hHprev := mrLogSchedule_resolution_four_le heta1 (by linarith : 0 ≤ p₁) hlogq hbudget
    (show 1 ≤ j - 1 by omega)
  apply mrScheduled_firstSmallClass_rectangle_energy_le heta0 heta1 hp hqexp hpq hbudget hj
    (mrScheduledPrimeSubblock eta p₁ q₁) (fun _ _ ↦ mrFinitePrimeLineCoefficient f)
    (fun r ↦ mrScheduledTypicalCofactor blocks eta p₁ q₁ j r X)
    (fun _ ↦ mrFiniteCofactorLineCoefficient (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f)
    (fun r _ ↦ mrScheduledPrimeSubblock_prime eta p₁ q₁ (j - 1) r) ?_ ?_ ?_ ?_ hX
    (mrScheduledNarrowInterval eta p₁ q₁ j) ?_ ?_ ?_ ?_ hT
  · intro r hr p hpP
    exact norm_mrFinitePrimeLineCoefficient_le hbound
      (mrScheduledPrimeSubblock_prime eta p₁ q₁ (j - 1) r p hpP).pos
  · intro r hr m hm
    exact norm_mrFiniteCofactorLineCoefficient_le_inv hbound (mrTypicalCofactorRectangle_pos hm)
  · intro r hr p hpP
    exact (mrScheduledPrimeSubblock_dyadic_bounds (by linarith : 2 ≤ mrLogBlockResolution eta p₁ q₁ ((j - 1 : ℕ) : ℝ)) p hpP).1
  · intro r hr p hpP
    exact (mrScheduledPrimeSubblock_dyadic_bounds (by linarith : 2 ≤ mrLogBlockResolution eta p₁ q₁ ((j - 1 : ℕ) : ℝ)) p hpP).2
  · intro r hr
    exact mrNarrowPrimeInterval_upper_pos (by linarith : 0 < mrLogBlockResolution eta p₁ q₁ (j : ℝ)) r
  · intro r hr
    exact Nat.le_ceil _
  · intro r hr
    exact mrNarrowPrimeInterval_upper_le_exp_shift (by linarith : 1 ≤ mrLogBlockResolution eta p₁ q₁ (j : ℝ)) r
  · intro r hr
    exact mrTypicalCofactorRectangle_subset _ _ _ _

/-- The first class has the source base-case saving for the same actual
prime sets and cofactor coefficients. -/
theorem mrArithmetic_firstClass_product_energy_le
    (blocks : Finset (ℕ × ℕ))
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) (hscale : Real.exp q₁ ≤ X) {T : ℝ} (hT : 0 ≤ T) :
    mrLogBlockResolution eta p₁ q₁ 1 * q₁ *
      (∑ r ∈ mrScheduledSubblocks eta p₁ q₁ 1, ∫ t in -T..T,
        (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) 1).indicator
          (fun t ↦ ‖logarithmicDirichletPolynomial (mrScheduledPrimeSubblock eta p₁ q₁ 1 r)
              (mrFinitePrimeLineCoefficient f) t *
            logarithmicDirichletPolynomial (mrScheduledTypicalCofactor blocks eta p₁ q₁ 1 r X)
              (mrFiniteCofactorLineCoefficient (primesInBlock (mrScheduledPrimeInterval p₁ q₁ 1)) f) t‖ ^ 2) t) ≤
      256 * Real.exp 1 * (1 + Real.pi) * (T / X * Real.exp q₁ + 1) *
        Real.exp (Real.log q₁ / 3 - (1 / 6 - eta) * p₁) := by
  have hq : 1 ≤ q₁ := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hqexp
  have hlogq : 1 ≤ Real.log q₁ := by
    have hh := Real.log_le_log (Real.exp_pos 1) hqexp
    rwa [Real.log_exp] at hh
  have hH := mrLogSchedule_resolution_four_le heta1 (by linarith : 0 ≤ p₁) hlogq hbudget
    (by norm_num : 1 ≤ (1 : ℕ))
  have hparam (r : ℕ) (hr : r ∈ mrScheduledSubblocks eta p₁ q₁ 1) :
      mrScheduledParameter eta p₁ q₁ 1 r ≤ q₁ := by
    have hh := (mrScheduledParameter_bounds heta1 hp hq hlogq hbudget (by norm_num : 1 ≤ (1 : ℕ)) hr).2
    simpa only [mrLogScheduleUpper, Nat.cast_one, one_pow, one_mul, pow_one] using hh
  apply mrScheduled_firstClass_rectangle_energy_le heta0 heta1 hp hqexp hbudget
    (mrScheduledPrimeSubblock eta p₁ q₁) (fun _ _ ↦ mrFinitePrimeLineCoefficient f)
    (mrScheduledNarrowInterval eta p₁ q₁ 1)
    (fun r ↦ mrScheduledTypicalCofactor blocks eta p₁ q₁ 1 r X)
    (fun _ ↦ mrFiniteCofactorLineCoefficient (primesInBlock (mrScheduledPrimeInterval p₁ q₁ 1)) f)
    hX ?_ ?_ ?_ ?_ ?_ ?_ ?_ hT
  · intro r hr
    exact mrNarrowPrimeInterval_lower_pos _ _
  · intro r hr
    exact mrNarrowPrimeInterval_upper_pos (by linarith : 0 < mrLogBlockResolution eta p₁ q₁ ((1 : ℕ) : ℝ)) r
  · intro r hr
    apply Nat.ceil_le.mpr
    exact (Real.exp_le_exp.mpr (hparam r hr)).trans hscale
  · intro r hr
    exact mrNarrowPrimeInterval_dyadic_width (by linarith : 2 ≤ mrLogBlockResolution eta p₁ q₁ ((1 : ℕ) : ℝ)) r
  · intro r hr
    apply (mrNarrowPrimeInterval_upper_le_exp_shift (by linarith : 1 ≤ mrLogBlockResolution eta p₁ q₁ ((1 : ℕ) : ℝ)) r).trans
    exact Real.exp_le_exp.mpr (add_le_add (hparam r hr) le_rfl)
  · intro r hr
    exact mrTypicalCofactorRectangle_subset _ _ _ _
  · intro r hr m hm
    exact norm_mrFiniteCofactorLineCoefficient_le_inv hbound (mrTypicalCofactorRectangle_pos hm)

/-- All actual narrow subblock boundaries have a common energy budget
of order `(T/X+1)(1/H_j+1/X)`. -/
theorem mrArithmetic_combinedBoundary_energy_le
    (blocks : Finset (ℕ × ℕ))
    {eta p₁ q₁ : ℝ} (heta1 : eta ≤ 1 / 12) (hp : 0 ≤ p₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 1 ≤ j)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖∑ r ∈ mrScheduledSubblocks eta p₁ q₁ j,
      mrTypicalRamareBoundaryPolynomial blocks (mrScheduledPrimeInterval p₁ q₁ j)
        (mrScheduledNarrowInterval eta p₁ q₁ j r) (mrScheduledPrimeSubblock eta p₁ q₁ j r) f X t‖ ^ 2) ≤
      32 * (1 + Real.pi) * (T / X + 1) *
        (6 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) + 1 / X) := by
  have hH := mrLogSchedule_resolution_four_le heta1 hp hlogq hbudget hj
  have hH0 : 0 < mrLogBlockResolution eta p₁ q₁ (j : ℝ) := by linarith
  have heps : 2 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hH0).mpr
    linarith
  have hh := intervalIntegral_sum_mrTypicalRamareBoundaryPolynomial_le
    (mrScheduledSubblocks eta p₁ q₁ j) blocks (mrScheduledPrimeInterval p₁ q₁ j)
    (mrScheduledNarrowInterval eta p₁ q₁ j) (mrScheduledPrimeSubblock eta p₁ q₁ j)
    hbound hX (by positivity : 0 ≤ 2 / mrLogBlockResolution eta p₁ q₁ (j : ℝ)) heps
    (fun r _ ↦ mrNarrowPrimeInterval_lower_pos _ _)
    (fun r _ ↦ mrNarrowPrimeInterval_relative_width (by linarith : 2 ≤ mrLogBlockResolution eta p₁ q₁ (j : ℝ)) r)
    (fun r _ ↦ mrScheduledPrimeSubblock_integer_bounds hH0)
    (fun r _ ↦ mrScheduledPrimeSubblock_subset eta p₁ q₁ j r)
    (mrScheduledPrimeSubblock_partition eta p₁ q₁ j).1 hT
  simpa only [show (3 : ℝ) * (2 / mrLogBlockResolution eta p₁ q₁ (j : ℝ)) =
    6 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) by ring] using hh

end Erdos67b
