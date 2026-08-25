import ErdosProblems.Erdos67.MRHalaszThreeBandEuler

/-!
# Integrating a frequency-dependent three-band choice

The small Euler factor in the three-band argument can vary with the
frequency.  This file removes any measurable-selection issue: pointwise,
the square of the triple product is bounded by the sum of the three
pair-product squares, multiplied by the common `L∞` bound squared.  The
inequality is then integrated on a vertical segment.
-/

open scoped BigOperators ComplexConjugate Interval
open Complex
open MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67.EulerResidue Erdos67.MRHalaszEuler

theorem normSq_three_mul_le_of_one_norm_le
    (a b c : ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hsmall : ‖a‖ ≤ M ∨ ‖b‖ ≤ M ∨ ‖c‖ ≤ M) :
    Complex.normSq (a * b * c) ≤
      M ^ 2 *
        (Complex.normSq (a * b) + Complex.normSq (a * c) +
          Complex.normSq (b * c)) := by
  have ha : 0 ≤ Complex.normSq a := Complex.normSq_nonneg a
  have hb : 0 ≤ Complex.normSq b := Complex.normSq_nonneg b
  have hc : 0 ≤ Complex.normSq c := Complex.normSq_nonneg c
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  simp only [Complex.normSq_mul]
  rcases hsmall with hsmall | hsmall | hsmall
  · have hs : Complex.normSq a ≤ M ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_sq₀ (norm_nonneg _) hM).2 hsmall
    have hbc : 0 ≤ Complex.normSq b * Complex.normSq c :=
      mul_nonneg hb hc
    calc
      Complex.normSq a * Complex.normSq b * Complex.normSq c =
          Complex.normSq a *
            (Complex.normSq b * Complex.normSq c) := by ring
      _ ≤ M ^ 2 * (Complex.normSq b * Complex.normSq c) :=
        mul_le_mul_of_nonneg_right hs hbc
      _ ≤ M ^ 2 *
          (Complex.normSq a * Complex.normSq b +
            Complex.normSq a * Complex.normSq c +
              Complex.normSq b * Complex.normSq c) := by
        gcongr
        nlinarith [mul_nonneg ha hb, mul_nonneg ha hc]
  · have hs : Complex.normSq b ≤ M ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_sq₀ (norm_nonneg _) hM).2 hsmall
    have hac : 0 ≤ Complex.normSq a * Complex.normSq c :=
      mul_nonneg ha hc
    calc
      Complex.normSq a * Complex.normSq b * Complex.normSq c =
          Complex.normSq b *
            (Complex.normSq a * Complex.normSq c) := by ring
      _ ≤ M ^ 2 * (Complex.normSq a * Complex.normSq c) :=
        mul_le_mul_of_nonneg_right hs hac
      _ ≤ M ^ 2 *
          (Complex.normSq a * Complex.normSq b +
            Complex.normSq a * Complex.normSq c +
              Complex.normSq b * Complex.normSq c) := by
        gcongr
        nlinarith [mul_nonneg ha hb, mul_nonneg hb hc]
  · have hs : Complex.normSq c ≤ M ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_sq₀ (norm_nonneg _) hM).2 hsmall
    have hab : 0 ≤ Complex.normSq a * Complex.normSq b :=
      mul_nonneg ha hb
    calc
      Complex.normSq a * Complex.normSq b * Complex.normSq c ≤
          (Complex.normSq a * Complex.normSq b) * M ^ 2 :=
        mul_le_mul_of_nonneg_left hs hab
      _ ≤ M ^ 2 *
          (Complex.normSq a * Complex.normSq b +
            Complex.normSq a * Complex.normSq c +
              Complex.normSq b * Complex.normSq c) := by
        rw [mul_comm (Complex.normSq a * Complex.normSq b) (M ^ 2)]
        gcongr
        nlinarith [mul_nonneg ha hc, mul_nonneg hb hc]

/-- Integrated form of `normSq_three_mul_le_of_one_norm_le`.  It is useful
when the identity of the small factor varies with `t`. -/
theorem intervalIntegral_normSq_three_mul_le_pair_sum
    (f g k : ℝ → ℂ) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hf : Continuous f) (hg : Continuous g) (hk : Continuous k)
    (hsmall : ∀ t, |t| ≤ T →
      ‖f t‖ ≤ M ∨ ‖g t‖ ≤ M ∨ ‖k t‖ ≤ M) :
    (∫ t in -T..T, Complex.normSq (f t * g t * k t)) ≤
      M ^ 2 *
        ((∫ t in -T..T, Complex.normSq (f t * g t)) +
          (∫ t in -T..T, Complex.normSq (f t * k t)) +
          ∫ t in -T..T, Complex.normSq (g t * k t)) := by
  have hle : -T ≤ T := by linarith
  have hleft : IntervalIntegrable
      (fun t ↦ Complex.normSq (f t * g t * k t)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hright : IntervalIntegrable
      (fun t ↦ M ^ 2 *
        (Complex.normSq (f t * g t) + Complex.normSq (f t * k t) +
          Complex.normSq (g t * k t))) volume (-T) T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hfg : IntervalIntegrable
      (fun t ↦ Complex.normSq (f t * g t)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hfk : IntervalIntegrable
      (fun t ↦ Complex.normSq (f t * k t)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hgk : IntervalIntegrable
      (fun t ↦ Complex.normSq (g t * k t)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    (∫ t in -T..T, Complex.normSq (f t * g t * k t)) ≤
        ∫ t in -T..T, M ^ 2 *
          (Complex.normSq (f t * g t) + Complex.normSq (f t * k t) +
            Complex.normSq (g t * k t)) := by
      apply intervalIntegral.integral_mono_on hle hleft hright
      intro t ht
      apply normSq_three_mul_le_of_one_norm_le _ _ _ hM
      apply hsmall t
      exact abs_le.mpr ⟨ht.1, ht.2⟩
    _ = M ^ 2 *
        ((∫ t in -T..T, Complex.normSq (f t * g t)) +
          (∫ t in -T..T, Complex.normSq (f t * k t)) +
          ∫ t in -T..T, Complex.normSq (g t * k t)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_add (hfg.add hfk) hgk,
        intervalIntegral.integral_add hfg hfk]

/-- A prime-band L-series is continuous along the Halász vertical line.
The proof deliberately establishes absolute convergence on a slightly
larger half-plane before invoking the general Mathlib L-series API. -/
theorem continuous_LSeries_primeBand_halaszPoint
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P]
    {X : ℕ} (hX : 1 < X) :
    Continuous (fun t : ℝ ↦
      LSeries (primeBandCoefficient f P) (halaszPoint X t)) := by
  let sigma := taoExponent X
  have hsigma : 1 < sigma := one_lt_taoExponent hX
  have hmid : 1 < (sigma + 1) / 2 := by linarith
  have hsum : LSeriesSummable (primeBandCoefficient f P)
      (((sigma + 1) / 2 : ℝ) : ℂ) :=
    primeBandCoefficient_LSeriesSummable hbound P (by simpa using hmid)
  have habs : LSeries.abscissaOfAbsConv (primeBandCoefficient f P) <
      (sigma : ℝ) := by
    calc
      LSeries.abscissaOfAbsConv (primeBandCoefficient f P) ≤
          (((sigma + 1) / 2 : ℝ) : EReal) := by
        simpa using hsum.abscissaOfAbsConv_le
      _ < (sigma : ℝ) := by
        exact_mod_cast (by linarith : (sigma + 1) / 2 < sigma)
  have hline : Continuous (fun t : ℝ ↦ halaszPoint X t) := by
    unfold halaszPoint
    fun_prop
  exact (LSeries_differentiableOn (primeBandCoefficient f P)).continuousOn.comp_continuous
    hline (fun t ↦ by simpa [sigma, halaszPoint_re] using habs)

/-- Quantitative complete-series energy bound obtained by combining the
frequency-wise `A/3` Euler suppression with the selection-free integrated
three-band inequality.  Its right hand side contains only the three
pairwise band energies; these are the two `L²` factors controlled by the
prime-band sieve/mean-value argument. -/
theorem intervalIntegral_normSq_LSeries_le_threeBand_pair_sum
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {A X : ℕ} (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {T : ℝ} (hT : 0 ≤ T) (hTX : T ≤ X) :
    (∫ t in -T..T, Complex.normSq (LSeries f (halaszPoint X t))) ≤
      (threeBandEulerBound A X) ^ 2 *
        ((∫ t in -T..T, Complex.normSq
          (LSeries (primeBandCoefficient f P₁) (halaszPoint X t) *
            LSeries
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p))
              (halaszPoint X t))) +
        (∫ t in -T..T, Complex.normSq
          (LSeries (primeBandCoefficient f P₁) (halaszPoint X t) *
            LSeries
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p))
              (halaszPoint X t))) +
        ∫ t in -T..T, Complex.normSq
          (LSeries
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p))
              (halaszPoint X t) *
            LSeries
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p))
              (halaszPoint X t))) := by
  let f₁ : ℝ → ℂ := fun t ↦
    LSeries (primeBandCoefficient f P₁) (halaszPoint X t)
  let f₂ : ℝ → ℂ := fun t ↦
    LSeries (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p))
      (halaszPoint X t)
  let f₃ : ℝ → ℂ := fun t ↦
    LSeries (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p))
      (halaszPoint X t)
  have hc₁ : Continuous f₁ :=
    continuous_LSeries_primeBand_halaszPoint hbound P₁ hX
  have hc₂ : Continuous f₂ :=
    continuous_LSeries_primeBand_halaszPoint hbound
      (fun p ↦ ¬ P₁ p ∧ P₂ p) hX
  have hc₃ : Continuous f₃ :=
    continuous_LSeries_primeBand_halaszPoint hbound
      (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) hX
  have hsmall : ∀ t, |t| ≤ T →
      ‖f₁ t‖ ≤ threeBandEulerBound A X ∨
        ‖f₂ t‖ ≤ threeBandEulerBound A X ∨
        ‖f₃ t‖ ≤ threeBandEulerBound A X := by
    intro t ht
    apply one_threeBand_LSeries_small_of_nonpretentious
      hmul hbound P₁ P₂ hX hnonpret
    exact ht.trans (by exact_mod_cast hTX)
  have henergy := intervalIntegral_normSq_three_mul_le_pair_sum
    f₁ f₂ f₃ (Real.exp_pos _).le hT hc₁ hc₂ hc₃ hsmall
  have hseries (t : ℝ) : f₁ t * f₂ t * f₃ t =
      LSeries f (halaszPoint X t) := by
    rw [show f₁ t * f₂ t * f₃ t = f₁ t * (f₂ t * f₃ t) by ring]
    exact LSeries_threePrimeBands hmul hbound P₁ P₂
      (by rw [halaszPoint_re]; exact one_lt_taoExponent hX)
  have hident :
      (∫ t in -T..T, Complex.normSq (LSeries f (halaszPoint X t))) =
        ∫ t in -T..T, Complex.normSq (f₁ t * f₂ t * f₃ t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change Complex.normSq (LSeries f (halaszPoint X t)) =
      Complex.normSq (f₁ t * f₂ t * f₃ t)
    rw [hseries]
  change (∫ t in -T..T, Complex.normSq (LSeries f (halaszPoint X t))) ≤ _
  rw [hident]
  exact henergy

end

end Erdos67.MRHalaszBands
