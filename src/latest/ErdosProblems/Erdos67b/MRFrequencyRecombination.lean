import ErdosProblems.Erdos67b.MRArithmeticFrequencyEnergy

/-!
# Measurable recombination with a grouped boundary

Cauchy--Schwarz is applied only to the prime--cofactor products. The
boundary stays grouped, so its energy retains the thin-support saving.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

/-- Recombination on a measurable class without a subblock-count factor
on the boundary energy. -/
theorem intervalIntegral_indicator_sum_sub_le
    {ι : Type*} (V : Finset ι) (Q : ι → ℝ → ℂ) (B : ℝ → ℂ)
    (hQ : ∀ v ∈ V, Continuous (Q v)) (hB : Continuous B)
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, E.indicator (fun t ↦ ‖(∑ v ∈ V, Q v t) - B t‖ ^ 2) t) ≤
      2 * (V.card : ℝ) * (∑ v ∈ V, ∫ t in -T..T, E.indicator (fun t ↦ ‖Q v t‖ ^ 2) t) +
        2 * ∫ t in -T..T, ‖B t‖ ^ 2 := by
  classical
  have hint {g : ℝ → ℂ} (hg : Continuous g) :
      IntervalIntegrable (E.indicator (fun t ↦ ‖g t‖ ^ 2)) volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp ((hg.norm.pow 2).intervalIntegrable (-T) T)).indicator hE
  have hsumCont : Continuous (fun t ↦ ∑ v ∈ V, Q v t) := continuous_finsetSum V hQ
  have hsumInt : IntervalIntegrable
      (fun t ↦ ∑ v ∈ V, E.indicator (fun t ↦ ‖Q v t‖ ^ 2) t) volume (-T) T := by
    have heq : (fun t ↦ ∑ v ∈ V, E.indicator (fun t ↦ ‖Q v t‖ ^ 2) t) =
        ∑ v ∈ V, E.indicator (fun t ↦ ‖Q v t‖ ^ 2) := by
      funext t
      simp only [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum V (fun v hv ↦ hint (hQ v hv))
  have hBint : IntervalIntegrable (fun t ↦ ‖B t‖ ^ 2) volume (-T) T :=
    (hB.norm.pow 2).intervalIntegrable (-T) T
  have hpoint (t : ℝ) :
      E.indicator (fun t ↦ ‖(∑ v ∈ V, Q v t) - B t‖ ^ 2) t ≤
        2 * (V.card : ℝ) * (∑ v ∈ V, E.indicator (fun t ↦ ‖Q v t‖ ^ 2) t) + 2 * ‖B t‖ ^ 2 := by
    by_cases ht : t ∈ E
    · simp only [Set.indicator_of_mem ht]
      have hsum : ‖∑ v ∈ V, Q v t‖ ^ 2 ≤ (V.card : ℝ) * ∑ v ∈ V, ‖Q v t‖ ^ 2 := by
        simpa only [Complex.normSq_eq_norm_sq] using normSq_finset_sum_le_card_mul_sum_normSq V (fun v ↦ Q v t)
      have hsub : ‖(∑ v ∈ V, Q v t) - B t‖ ^ 2 ≤ 2 * (‖∑ v ∈ V, Q v t‖ ^ 2 + ‖B t‖ ^ 2) := by
        simpa only [Complex.normSq_eq_norm_sq] using normSq_sub_le_two_mul_add (∑ v ∈ V, Q v t) (B t)
      nlinarith
    · simp only [Set.indicator_of_notMem ht, Finset.sum_const_zero, mul_zero, zero_add]
      positivity
  have hmono := intervalIntegral.integral_mono_on (by linarith : -T ≤ T)
    (hint (hsumCont.sub hB)) ((hsumInt.const_mul _).add (hBint.const_mul 2))
    (fun t _ ↦ hpoint t)
  calc
    _ ≤ ∫ t in -T..T,
        (2 * (V.card : ℝ) * (∑ v ∈ V, E.indicator (fun t ↦ ‖Q v t‖ ^ 2) t) + 2 * ‖B t‖ ^ 2) := hmono
    _ = _ := by
      rw [intervalIntegral.integral_add (hsumInt.const_mul _) (hBint.const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun v hv ↦ hint (hQ v hv))]

theorem intervalIntegral_indicator_sum_sub_le_weighted
    {ι : Type*} (V : Finset ι) (Q : ι → ℝ → ℂ) (B : ℝ → ℂ)
    (hQ : ∀ v ∈ V, Continuous (Q v)) (hB : Continuous B)
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T)
    {w : ℝ} (hcard : (V.card : ℝ) ≤ 2 * w) :
    (∫ t in -T..T, E.indicator (fun t ↦ ‖(∑ v ∈ V, Q v t) - B t‖ ^ 2) t) ≤
      4 * w * (∑ v ∈ V, ∫ t in -T..T, E.indicator (fun t ↦ ‖Q v t‖ ^ 2) t) +
        2 * ∫ t in -T..T, ‖B t‖ ^ 2 := by
  have hnonneg : 0 ≤ ∑ v ∈ V, ∫ t in -T..T, E.indicator (fun t ↦ ‖Q v t‖ ^ 2) t := by
    apply Finset.sum_nonneg
    intro v hv
    apply intervalIntegral.integral_nonneg (by linarith : -T ≤ T)
    intro t ht
    exact Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
  apply (intervalIntegral_indicator_sum_sub_le V Q B hQ hB hE hT).trans
  have hh := mul_le_mul_of_nonneg_right hcard hnonneg
  nlinarith

noncomputable section

def mrScheduledCommonPolynomial
    (blocks : Finset (ℕ × ℕ)) (p₁ q₁ : ℝ) (j : ℕ) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
    (fun n ↦ mrTypicalCommonCoefficient blocks (2 * X)
      (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f n / (n : ℂ)) t

def mrScheduledProductPolynomial
    (blocks : Finset (ℕ × ℕ)) (eta p₁ q₁ : ℝ) (j r : ℕ) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (mrScheduledPrimeSubblock eta p₁ q₁ j r)
      (mrFinitePrimeLineCoefficient f) t *
    logarithmicDirichletPolynomial (mrScheduledTypicalCofactor blocks eta p₁ q₁ j r X)
      (mrFiniteCofactorLineCoefficient (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f) t

def mrScheduledBoundaryPolynomial
    (blocks : Finset (ℕ × ℕ)) (eta p₁ q₁ : ℝ) (j : ℕ) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) : ℂ :=
  ∑ r ∈ mrScheduledSubblocks eta p₁ q₁ j,
    mrTypicalRamareBoundaryPolynomial blocks (mrScheduledPrimeInterval p₁ q₁ j)
      (mrScheduledNarrowInterval eta p₁ q₁ j r) (mrScheduledPrimeSubblock eta p₁ q₁ j r) f X t

/-- The actual common-coefficient polynomial on any measurable frequency
set, with every boundary term paid by the common thin-band estimate. -/
theorem mrArithmetic_common_frequency_energy_le
    (blocks : Finset (ℕ × ℕ))
    {eta p₁ q₁ : ℝ} (heta1 : eta ≤ 1 / 12) (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 1 ≤ j)
    (hdisj : ∀ K ∈ blocks, K ≠ mrScheduledPrimeInterval p₁ q₁ j →
      Disjoint (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) (primesInBlock K))
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, E.indicator (fun t ↦ ‖mrScheduledCommonPolynomial blocks p₁ q₁ j f X t‖ ^ 2) t) ≤
      4 * (mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j *
        (∑ r ∈ mrScheduledSubblocks eta p₁ q₁ j, ∫ t in -T..T,
          E.indicator (fun t ↦ ‖mrScheduledProductPolynomial blocks eta p₁ q₁ j r f X t‖ ^ 2) t)) +
        64 * (1 + Real.pi) * (T / X + 1) *
          (6 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) + 1 / X) := by
  have hq : 1 ≤ q₁ := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hqexp
  have hlogq : 1 ≤ Real.log q₁ := by
    have hh := Real.log_le_log (Real.exp_pos 1) hqexp
    rwa [Real.log_exp] at hh
  have hH := mrLogSchedule_resolution_four_le heta1 (by linarith : 0 ≤ p₁) hlogq hbudget hj
  have hH0 : 0 < mrLogBlockResolution eta p₁ q₁ (j : ℝ) := by linarith
  have hqj : 1 ≤ mrLogScheduleUpper q₁ j := hq.trans (mrLogScheduleUpper_ge hq hj)
  have hweight : 1 ≤ mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j := by
    nlinarith
  let V := mrScheduledSubblocks eta p₁ q₁ j
  let Q := fun r ↦ mrScheduledProductPolynomial blocks eta p₁ q₁ j r f X
  let B := mrScheduledBoundaryPolynomial blocks eta p₁ q₁ j f X
  have hQ : ∀ r ∈ V, Continuous (Q r) := by
    intro r hr
    exact (continuous_logarithmicDirichletPolynomial _ _).mul (continuous_logarithmicDirichletPolynomial _ _)
  have hB : Continuous B := by
    apply continuous_finsetSum
    intro r hr
    exact continuous_logarithmicDirichletPolynomial _ _
  have hfactor (t : ℝ) : mrScheduledCommonPolynomial blocks p₁ q₁ j f X t =
      (∑ r ∈ V, Q r t) - B t := by
    have hh := mrTypicalCommonPolynomial_eq_products_sub_boundary
      (mrScheduledPrimeSubblock_partition eta p₁ q₁ j).1
      (mrScheduledPrimeSubblock_partition eta p₁ q₁ j).2
      (fun r _ ↦ mrNarrowPrimeInterval_lower_pos _ _)
      (fun r _ ↦ mrScheduledPrimeSubblock_integer_bounds hH0) hdisj f X t
    dsimp only [mrScheduledCommonPolynomial, V, Q, B, mrScheduledProductPolynomial,
      mrScheduledBoundaryPolynomial, mrScheduledTypicalCofactor, mrScheduledNarrowInterval]
    simpa only [Finset.sum_sub_distrib] using hh
  have hcard : (V.card : ℝ) ≤ 2 * (mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j) := by
    dsimp only [V, mrScheduledSubblocks]
    simpa only [mul_assoc] using card_mrLogBlockIndices_le
      (p := mrLogScheduleLower p₁ q₁ j) hweight
  have hbase := intervalIntegral_indicator_sum_sub_le_weighted V Q B hQ hB hE hT hcard
  have hboundary := mrArithmetic_combinedBoundary_energy_le blocks heta1 (by linarith : 0 ≤ p₁)
    hlogq hbudget hj hbound hX hT
  simp_rw [hfactor]
  calc
    _ ≤ 4 * (mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j) *
        (∑ r ∈ V, ∫ t in -T..T, E.indicator (fun t ↦ ‖Q r t‖ ^ 2) t) +
          2 * ∫ t in -T..T, ‖B t‖ ^ 2 := hbase
    _ ≤ 4 * (mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j) *
        (∑ r ∈ V, ∫ t in -T..T, E.indicator (fun t ↦ ‖Q r t‖ ^ 2) t) +
          2 * (32 * (1 + Real.pi) * (T / X + 1) *
            (6 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) + 1 / X)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hboundary (by norm_num))
    _ = _ := by dsimp only [V, Q]; ring

/-- Recombined higher first-small class for the actual finite scheduled
block family. All support, partition and other-block conditions are proved. -/
theorem mrArithmetic_common_firstSmallClass_energy_le
    (J : ℕ) {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) j).indicator
      (fun t ↦ ‖mrScheduledCommonPolynomial (mrScheduledBlocks p₁ q₁ J) p₁ q₁ j f X t‖ ^ 2) t) ≤
      2048 * Real.exp 13 * (1 + Real.pi) * (T / X + 1) /
        ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1))) +
      64 * (1 + Real.pi) * (T / X + 1) *
        (6 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) + 1 / X) := by
  have hq : 1 ≤ q₁ := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hqexp
  have hlogq : 1 ≤ Real.log q₁ := by
    have hh := Real.log_le_log (Real.exp_pos 1) hqexp
    rwa [Real.log_exp] at hh
  have hmeas : MeasurableSet (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) j) :=
    MeasurableSet.disjointed (measurableSet_mrScheduledSmallFrequencySet _ _ _ _ _) j
  have hbase := mrArithmetic_common_frequency_energy_le (mrScheduledBlocks p₁ q₁ J)
    heta1 hp hqexp hbudget (show 1 ≤ j by omega)
    (mrScheduledBlocks_other_disjoint heta1 hp hq hpq hlogq hbudget J (by omega)) hbound hX hmeas hT
  have hprod := mrArithmetic_firstSmallClass_product_energy_le (mrScheduledBlocks p₁ q₁ J)
    heta0 heta1 hp hqexp hpq hbudget hj hbound hX hT
  apply hbase.trans
  have hh := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 4)
  dsimp only [mrScheduledProductPolynomial]
  calc
    _ ≤ 4 * (512 * Real.exp 13 * (1 + Real.pi) * (T / X + 1) /
        ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1)))) +
      64 * (1 + Real.pi) * (T / X + 1) *
        (6 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) + 1 / X) := add_le_add hh le_rfl
    _ = _ := by ring

/-- Recombined first class with the source first-block decay and the
combined endpoint error. -/
theorem mrArithmetic_common_firstClass_energy_le
    (J : ℕ) {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) (hscale : Real.exp q₁ ≤ X) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) 1).indicator
      (fun t ↦ ‖mrScheduledCommonPolynomial (mrScheduledBlocks p₁ q₁ J) p₁ q₁ 1 f X t‖ ^ 2) t) ≤
      1024 * Real.exp 1 * (1 + Real.pi) * (T / X * Real.exp q₁ + 1) *
        Real.exp (Real.log q₁ / 3 - (1 / 6 - eta) * p₁) +
      64 * (1 + Real.pi) * (T / X + 1) *
        (6 / mrLogBlockResolution eta p₁ q₁ 1 + 1 / X) := by
  have hq : 1 ≤ q₁ := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hqexp
  have hlogq : 1 ≤ Real.log q₁ := by
    have hh := Real.log_le_log (Real.exp_pos 1) hqexp
    rwa [Real.log_exp] at hh
  have hmeas : MeasurableSet (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) 1) :=
    MeasurableSet.disjointed (measurableSet_mrScheduledSmallFrequencySet _ _ _ _ _) 1
  have hbase := mrArithmetic_common_frequency_energy_le (mrScheduledBlocks p₁ q₁ J)
    heta1 hp hqexp hbudget (by norm_num : 1 ≤ (1 : ℕ))
    (mrScheduledBlocks_other_disjoint heta1 hp hq hpq hlogq hbudget J (by norm_num)) hbound hX hmeas hT
  have hprod := mrArithmetic_firstClass_product_energy_le (mrScheduledBlocks p₁ q₁ J)
    heta0 heta1 hp hqexp hbudget hbound hX hscale hT
  have hupper : mrLogScheduleUpper q₁ 1 = q₁ := by norm_num [mrLogScheduleUpper]
  simp only [Nat.cast_one, hupper] at hbase
  apply hbase.trans
  have hh := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 4)
  dsimp only [mrScheduledProductPolynomial]
  calc
    _ ≤ 4 * (256 * Real.exp 1 * (1 + Real.pi) * (T / X * Real.exp q₁ + 1) *
        Real.exp (Real.log q₁ / 3 - (1 / 6 - eta) * p₁)) +
      64 * (1 + Real.pi) * (T / X + 1) *
        (6 / mrLogBlockResolution eta p₁ q₁ 1 + 1 / X) := add_le_add hh le_rfl
    _ = _ := by ring

end

end Erdos67b
