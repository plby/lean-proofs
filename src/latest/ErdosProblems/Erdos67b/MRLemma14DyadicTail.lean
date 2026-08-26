import ErdosProblems.Erdos67b.MRLemma14MeanTail
import ErdosProblems.Erdos67b.MRLemma14ScaledLow
import ErdosProblems.Erdos67b.MRFiniteRamareFactorization

/-!
# Actual dyadic-polynomial tails and the short-interval bound

The square mass is bounded on the exact restricted support. The finite
mean-value theorem and reflection of the symmetric frequency interval
then discharge the weighted far-tail hypothesis of the Perron adapter.
-/

open Finset MeasureTheory Set

namespace Erdos67b

noncomputable section

theorem sum_normSq_dyadicRestricted_div_le
    (S : Finset ℕ) {f : ℕ → ℂ} (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y : ℕ} (hY : 0 < Y) :
    (∑ n ∈ dyadicRestrictedSupport S Y, Complex.normSq (f n / (n : ℂ))) ≤
      (Y : ℝ)⁻¹ := by
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hcard : (dyadicRestrictedSupport S Y).card ≤ Y := by
    have hh := Finset.card_le_card (Finset.inter_subset_left (s₁ := Finset.Ioc Y (2 * Y))
      (s₂ := S))
    simpa [dyadicRestrictedSupport, show 2 * Y - Y = Y by omega] using hh
  calc
    _ ≤ ∑ _n ∈ dyadicRestrictedSupport S Y, (Y : ℝ)⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnY := (Finset.mem_Ioc.mp (Finset.mem_inter.mp hn).1).1
      have hn0 : 0 < n := hY.trans hnY
      have hnorm : ‖f n / (n : ℂ)‖ ≤ (n : ℝ)⁻¹ := by
        rw [norm_div, Complex.norm_natCast]
        simpa only [one_div] using
          (div_le_div_of_nonneg_right (hf n hn0) (Nat.cast_nonneg n))
      have hinv : (n : ℝ)⁻¹ ≤ (Y : ℝ)⁻¹ := inv_anti₀ hYR (by exact_mod_cast hnY.le)
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hinv) 2
    _ = ((dyadicRestrictedSupport S Y).card : ℝ) * (Y : ℝ)⁻¹ ^ 2 := by simp
    _ ≤ (Y : ℝ) * (Y : ℝ)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
    _ = _ := by field_simp

/-- The actual vertical polynomial has the expected linear finite mean bound. -/
theorem intervalIntegral_normSq_dyadicVerticalDirichletPolynomial_le
    (S : Finset ℕ) {f : ℕ → ℂ} (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y : ℕ} (hY : 0 < Y) {V : ℝ} (hV : 0 ≤ V) :
    (∫ t in -V..V, Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) ≤
      2 * V / Y + 4 * Real.pi := by
  let D := dyadicRestrictedSupport S Y
  let b : ℕ → ℂ := fun n ↦ f n / (n : ℂ)
  have hmass := sum_normSq_dyadicRestricted_div_le S hf hY
  have hmean := norm_logarithmicDirichletPolynomial_intervalIntegral_le_support (A := D)
    (show 0 < 2 * Y by omega)
    (fun n hn ↦ hY.trans (Finset.mem_Ioc.mp (Finset.mem_inter.mp hn).1).1)
    (fun n hn ↦ (Finset.mem_Ioc.mp (Finset.mem_inter.mp hn).1).2) b hV
  calc
    _ = ∫ t in -V..V, Complex.normSq (logarithmicDirichletPolynomial D b t) :=
      symmetricVerticalEnergy_dyadicVerticalDirichletPolynomial S f Y V
    _ = ‖∫ t in -V..V, (starRingEnd ℂ) (logarithmicDirichletPolynomial D b t) *
          logarithmicDirichletPolynomial D b t‖ := by
      simpa only [Complex.normSq_eq_norm_sq] using
        (intervalIntegral_norm_sq_eq_norm_conj_mul_self (logarithmicDirichletPolynomial D b) hV)
    _ ≤ (2 * V + 2 * Real.pi * (2 * Y : ℕ)) *
        ∑ n ∈ D, Complex.normSq (b n) := hmean
    _ ≤ (2 * V + 2 * Real.pi * (2 * Y : ℕ)) * (Y : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by push_cast; field_simp; ring

/-- Uniform finite far-tail bound, with its full ambient-scale saving. -/
theorem lemma14TwoSidedWeightedTail_dyadic_le_mean
    (S : Finset ℕ) {f : ℕ → ℂ} (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y : ℕ} (hY : 0 < Y) {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U) :
    lemma14TwoSidedWeightedTail (dyadicVerticalDirichletPolynomial S f Y) T U ≤
      16 / ((Y : ℝ) * T) + 16 * Real.pi / T ^ 2 := by
  have hmean (V : ℝ) (hV : 0 ≤ V) :
      (∫ t in -V..V, Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) ≤
        (2 / (Y : ℝ)) * V + 4 * Real.pi := by
    convert intervalIntegral_normSq_dyadicVerticalDirichletPolynomial_le S hf hY hV using 1
    ring
  have hh := lemma14TwoSidedWeightedTail_le_of_mean
    (dyadicVerticalDirichletPolynomial S f Y)
    (continuous_dyadicVerticalDirichletPolynomial S f Y)
    (by positivity : 0 ≤ 2 / (Y : ℝ)) (by positivity : 0 ≤ 4 * Real.pi) hT hTU hmean
  convert hh using 1
  ring

/-- The actual short-sum bound with the far-tail input completely discharged. -/
theorem normalized_uncenteredShortIntervalMeanSquare_le_scaled_low_add_meanTail
    (S : Finset ℕ) {f : ℕ → ℂ} (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y X H : ℕ} (hY : 0 < Y) (hH : 0 < H) (hHX : H ≤ X)
    {T : ℝ} (hT : 0 < T) :
    uncenteredShortIntervalMeanSquare (dyadicRestrictedCoefficient S f Y) X H /
        (H : ℝ) ^ 2 ≤
      2 * lemma14UniversalScaledLowConstant * ((X : ℝ) + 1) *
        (∫ t in -T..T, Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
      4 * (lemma14UniversalScaledHighConstant * ((X : ℝ) + 1) ^ 3 /
        (H : ℝ) ^ 2) * (16 / ((Y : ℝ) * T) + 16 * Real.pi / T ^ 2) := by
  apply normalized_uncenteredShortIntervalMeanSquare_le_scaled_low_add_weightedHigh
    S f Y hH hHX hT (by positivity)
  intro U hTU
  exact lemma14TwoSidedWeightedTail_dyadic_le_mean S hf hY hT hTU

end

end Erdos67b
