/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierLocalFactor

/-!
# Comparing the arithmetic local polynomial with its singular factor

The reference product and the arithmetic polynomial have the same linear
variation in their pair coefficients.  This file keeps that variation
separate from the quadratic remainder before dividing by the reference.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def pairProductErrorConstant (n : ℕ) : ℝ := (7 * (n : ℝ)) ^ 2 + 8 * n

theorem pairProductErrorConstant_nonneg (n : ℕ) :
    0 ≤ pairProductErrorConstant n := by
  unfold pairProductErrorConstant
  positivity

theorem norm_one_sub_complex_inv_le_one {p : ℝ} (hp : 2 ≤ p) :
    ‖1 - 1 / (p : ℂ)‖ ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hpos : 0 ≤ 1 - 1 / p := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
    linarith
  have heq : (1 : ℂ) - 1 / (p : ℂ) = ((1 - 1 / p : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  have : 0 ≤ (1 : ℝ) / p := by positivity
  linarith

theorem norm_zeroExponentPairProduct_le_one (n : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    ‖(1 - 1 / (p : ℂ)) ^ n‖ ≤ 1 := by
  rw [norm_pow]
  simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_one_sub_complex_inv_le_one hp) n

theorem pow_half_le_norm_zeroExponentPairProduct (n : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    (1 / 2 : ℝ) ^ n ≤ ‖(1 - 1 / (p : ℂ)) ^ n‖ := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (by norm_num)
    (half_le_norm_one_sub_complex_div hp (X := 1) (by simp)) n

theorem norm_zeroExponentPairProduct_error_le
    {ι : Type*} (s : Finset ι) {p : ℝ}
    (hp : 2 ≤ p) (hcard : 7 * (s.card : ℝ) ≤ p) :
    ‖(1 - 1 / (p : ℂ)) ^ s.card - (1 - (s.card : ℂ) / p)‖ ≤
      pairProductErrorConstant s.card / p ^ 2 := by
  have h := norm_prod_selbergPairZetaFactor_error_le s
    (fun _ ↦ 1) (fun _ ↦ 1) hp hcard (by simp) (by simp)
  have hpairs : (∏ _i ∈ s, selbergPairZetaFactor p 1 1) =
      (1 - 1 / (p : ℂ)) ^ s.card := by
    simp [selbergPairZetaFactor_at_zero_exponents hp]
  rw [hpairs] at h
  simpa [selbergPairPolynomial, pairProductErrorConstant, sub_eq_add_neg, neg_div] using h

theorem norm_pairPolynomial_linearVariation_le
    {ι : Type*} (s : Finset ι) (X Y : ι → ℂ) {p : ℝ} (hp : 0 < p)
    (hX : ∀ i ∈ s, ‖X i‖ ≤ 1) (hY : ∀ i ∈ s, ‖Y i‖ ≤ 1) :
    ‖((∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) + (s.card : ℂ)) / p‖ ≤
      4 * (s.card : ℝ) / p := by
  have hsum : ‖∑ i ∈ s, selbergPairPolynomial (X i) (Y i)‖ ≤
      3 * (s.card : ℝ) := by
    calc
      _ ≤ ∑ i ∈ s, ‖selbergPairPolynomial (X i) (Y i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, (3 : ℝ) := Finset.sum_le_sum fun i hi ↦
        norm_selbergPairPolynomial_le_three (hX i hi) (hY i hi)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  calc
    _ ≤ ‖∑ i ∈ s, selbergPairPolynomial (X i) (Y i)‖ + ‖(s.card : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ 3 * (s.card : ℝ) + s.card := by simpa using add_le_add hsum (le_refl ‖(s.card : ℂ)‖)
    _ = _ := by ring

/-- The two reference products differ by their common linear variation
plus a genuinely quadratic, uniformly bounded remainder. -/
theorem norm_pairProduct_variation_remainder_le
    {ι : Type*} (s : Finset ι) (X Y : ι → ℂ) {p : ℝ}
    (hp : 2 ≤ p) (hcard : 7 * (s.card : ℝ) ≤ p)
    (hX : ∀ i ∈ s, ‖X i‖ ≤ 1) (hY : ∀ i ∈ s, ‖Y i‖ ≤ 1) :
    ‖(∏ i ∈ s, selbergPairZetaFactor p (X i) (Y i)) -
        (1 - 1 / (p : ℂ)) ^ s.card -
        ((∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) + (s.card : ℂ)) / p‖ ≤
      2 * pairProductErrorConstant s.card / p ^ 2 := by
  have heq : (∏ i ∈ s, selbergPairZetaFactor p (X i) (Y i)) -
      (1 - 1 / (p : ℂ)) ^ s.card -
      ((∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) + (s.card : ℂ)) / p =
      ((∏ i ∈ s, selbergPairZetaFactor p (X i) (Y i)) -
        (1 + (∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) / p)) -
      ((1 - 1 / (p : ℂ)) ^ s.card - (1 - (s.card : ℂ) / p)) := by ring
  rw [heq]
  calc
    _ ≤ _ + _ := norm_sub_le _ _
    _ ≤ pairProductErrorConstant s.card / p ^ 2 +
        pairProductErrorConstant s.card / p ^ 2 := by
      exact add_le_add (norm_prod_selbergPairZetaFactor_error_le s X Y hp hcard hX hY)
        (norm_zeroExponentPairProduct_error_le s hp hcard)
    _ = _ := by ring

theorem norm_zeroExponentPairProduct_sub_singularNumerator_le
    {ι : Type*} (s : Finset ι) {p : ℝ}
    (hp : 2 ≤ p) (hcard : 7 * (s.card : ℝ) ≤ p)
    {D : ℂ} (hD : ‖D‖ ≤ (s.card : ℝ)) :
    ‖(1 - 1 / (p : ℂ)) ^ s.card - (1 - ((s.card : ℂ) - D) / p)‖ ≤
      (pairProductErrorConstant s.card + s.card) / p := by
  have hp0 : 0 < p := by linarith
  have heq : (1 - 1 / (p : ℂ)) ^ s.card - (1 - ((s.card : ℂ) - D) / p) =
      ((1 - 1 / (p : ℂ)) ^ s.card - (1 - (s.card : ℂ) / p)) - D / p := by
    ring
  rw [heq]
  have hdiv : ‖D / (p : ℂ)‖ ≤ (s.card : ℝ) / p := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
    exact div_le_div_of_nonneg_right hD hp0.le
  calc
    _ ≤ _ + _ := norm_sub_le _ _
    _ ≤ pairProductErrorConstant s.card / p ^ 2 + (s.card : ℝ) / p :=
      add_le_add (norm_zeroExponentPairProduct_error_le s hp hcard) hdiv
    _ ≤ pairProductErrorConstant s.card / p + (s.card : ℝ) / p := by
      apply add_le_add _ le_rfl
      exact div_le_div_of_nonneg_left (pairProductErrorConstant_nonneg _) hp0
        (by nlinarith : p ≤ p ^ 2)
    _ = _ := by ring

theorem norm_singularNumerator_le_three (n : ℕ) {p : ℝ}
    (hp : 0 < p) (hn : (n : ℝ) ≤ p) {D : ℂ} (hD : ‖D‖ ≤ (n : ℝ)) :
    ‖1 - ((n : ℂ) - D) / (p : ℂ)‖ ≤ 3 := by
  have hdiff : ‖(n : ℂ) - D‖ ≤ 2 * (n : ℝ) := by
    calc
      _ ≤ ‖(n : ℂ)‖ + ‖D‖ := norm_sub_le _ _
      _ ≤ (n : ℝ) + n := by
        simpa using add_le_add (le_refl ‖(n : ℂ)‖) hD
      _ = _ := by ring
  have hquot : ‖((n : ℂ) - D) / (p : ℂ)‖ ≤ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    exact hdiff.trans (mul_le_mul_of_nonneg_left hn (by norm_num))
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖((n : ℂ) - D) / (p : ℂ)‖ := norm_sub_le _ _
    _ ≤ 3 := by rw [norm_one]; linarith

theorem half_le_norm_singularNumerator (n : ℕ) {p : ℝ}
    (hp : 0 < p) (hn : 4 * (n : ℝ) ≤ p) {D : ℂ} (hD : ‖D‖ ≤ (n : ℝ)) :
    (1 / 2 : ℝ) ≤ ‖1 - ((n : ℂ) - D) / (p : ℂ)‖ := by
  have hdiff : ‖(n : ℂ) - D‖ ≤ 2 * (n : ℝ) := by
    calc
      _ ≤ ‖(n : ℂ)‖ + ‖D‖ := norm_sub_le _ _
      _ ≤ (n : ℝ) + n := by simpa using add_le_add (le_refl ‖(n : ℂ)‖) hD
      _ = _ := by ring
  have hquot : ‖((n : ℂ) - D) / (p : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    linarith
  have h := norm_sub_norm_le (1 : ℂ) (((n : ℂ) - D) / (p : ℂ))
  rw [norm_one] at h
  linarith

theorem half_le_norm_zeroExponentSingularFactor (n : ℕ) {p : ℝ}
    (hp : 2 ≤ p) (hn : 4 * (n : ℝ) ≤ p) {D : ℂ} (hD : ‖D‖ ≤ (n : ℝ)) :
    (1 / 2 : ℝ) ≤
      ‖(1 - ((n : ℂ) - D) / (p : ℂ)) / (1 - 1 / (p : ℂ)) ^ n‖ := by
  have hp0 : 0 < p := by linarith
  have hlow := pow_half_le_norm_zeroExponentPairProduct n hp
  have hpos : 0 < ‖(1 - 1 / (p : ℂ)) ^ n‖ :=
    lt_of_lt_of_le (by positivity) hlow
  rw [norm_div]
  apply (le_div_iff₀ hpos).mpr
  calc
    _ ≤ (1 / 2 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (norm_zeroExponentPairProduct_le_one n hp) (by norm_num)
    _ ≤ _ := by simpa using half_le_norm_singularNumerator n hp0 hn hD

theorem norm_div_sub_one_le_twice_sub {z S : ℂ} (hS : (1 / 2 : ℝ) ≤ ‖S‖) :
    ‖z / S - 1‖ ≤ 2 * ‖z - S‖ := by
  have hS0 : S ≠ 0 := by
    intro h
    rw [h, norm_zero] at hS
    norm_num at hS
  rw [show z / S - 1 = (z - S) / S by rw [sub_div, div_self hS0], norm_div]
  calc
    _ ≤ ‖z - S‖ / (1 / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hS
    _ = _ := by ring

/-- The local quotient differs from its zero-exponent singular factor by
a reciprocal-square error and the first-order exceptional perturbation.
No exceptional term is discarded or reclassified as a quadratic error. -/
theorem norm_pairProduct_quotient_sub_singular_le
    {ι : Type*} (s : Finset ι) (X Y : ι → ℂ) {p : ℝ}
    (hp : 2 ≤ p) (hcard : 7 * (s.card : ℝ) ≤ p)
    (hX : ∀ i ∈ s, ‖X i‖ ≤ 1) (hY : ∀ i ∈ s, ‖Y i‖ ≤ 1)
    (E D : ℂ) (hD : ‖D‖ ≤ (s.card : ℝ)) :
    ‖(1 + ((∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) + E) / (p : ℂ)) /
        (∏ i ∈ s, selbergPairZetaFactor p (X i) (Y i)) -
        (1 - ((s.card : ℂ) - D) / p) / (1 - 1 / (p : ℂ)) ^ s.card‖ ≤
      (12 : ℝ) ^ s.card *
        ((4 * (s.card : ℝ) * (pairProductErrorConstant s.card + s.card) +
            6 * pairProductErrorConstant s.card) / p ^ 2 + ‖E - D‖ / p) := by
  let b := ∏ i ∈ s, selbergPairZetaFactor p (X i) (Y i)
  let b₀ := (1 - 1 / (p : ℂ)) ^ s.card
  let a := 1 - ((s.card : ℂ) - D) / (p : ℂ)
  let g := ((∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) + (s.card : ℂ)) / p
  let e := (E - D) / (p : ℂ)
  let r := b - b₀ - g
  let C := pairProductErrorConstant s.card
  have hC : 0 ≤ C := pairProductErrorConstant_nonneg _
  have hp0 : 0 < p := by linarith
  have hnp : (s.card : ℝ) ≤ p := by
    have hn0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    linarith
  have hbLow : (1 / 6 : ℝ) ^ s.card ≤ ‖b‖ :=
    pow_one_sixth_le_norm_prod_selbergPairZetaFactor s X Y hp hX hY
  have hb₀Low : (1 / 2 : ℝ) ^ s.card ≤ ‖b₀‖ :=
    pow_half_le_norm_zeroExponentPairProduct s.card hp
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hbLow
    have : (0 : ℝ) < (1 / 6 : ℝ) ^ s.card := by positivity
    linarith
  have hb₀0 : b₀ ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hb₀Low
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ s.card := by positivity
    linarith
  have hbRel : b₀ + g + r = b := by dsimp [r]; ring
  have hkRel : 1 + ((∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) + E) /
      (p : ℂ) = a + g + e := by dsimp [a, g, e]; ring
  have ha : ‖a‖ ≤ 3 := norm_singularNumerator_le_three s.card hp0 hnp hD
  have hb₀ : ‖b₀‖ ≤ 1 := norm_zeroExponentPairProduct_le_one s.card hp
  have hg : ‖g‖ ≤ 4 * (s.card : ℝ) / p :=
    norm_pairPolynomial_linearVariation_le s X Y hp0 hX hY
  have he : ‖e‖ = ‖E - D‖ / p := by
    simp only [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
  have hr : ‖r‖ ≤ 2 * C / p ^ 2 :=
    norm_pairProduct_variation_remainder_le s X Y hp hcard hX hY
  have hba : ‖b₀ - a‖ ≤ (C + (s.card : ℝ)) / p :=
    norm_zeroExponentPairProduct_sub_singularNumerator_le s hp hcard hD
  have hnum : ‖b₀ - a‖ * ‖g‖ + ‖b₀‖ * ‖e‖ + ‖a‖ * ‖r‖ ≤
      (4 * (s.card : ℝ) * (C + s.card) + 6 * C) / p ^ 2 + ‖E - D‖ / p := by
    rw [he]
    calc
      _ ≤ ((C + (s.card : ℝ)) / p) * (4 * (s.card : ℝ) / p) +
          1 * (‖E - D‖ / p) + 3 * (2 * C / p ^ 2) := by gcongr
      _ = _ := by ring
  have hden : (1 / 12 : ℝ) ^ s.card ≤ ‖b‖ * ‖b₀‖ := by
    rw [show (1 / 12 : ℝ) = (1 / 6) * (1 / 2) by norm_num, mul_pow]
    exact mul_le_mul hbLow hb₀Low (by positivity) (norm_nonneg _)
  have hcomparison := norm_quotient_linear_comparison_le a b₀ g e r hb₀0
    (by rwa [hbRel])
  rw [hbRel] at hcomparison
  change ‖(1 + ((∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) + E) /
      (p : ℂ)) / b - a / b₀‖ ≤ _
  rw [hkRel]
  calc
    _ ≤ (‖b₀ - a‖ * ‖g‖ + ‖b₀‖ * ‖e‖ + ‖a‖ * ‖r‖) / (‖b‖ * ‖b₀‖) :=
      hcomparison
    _ ≤ ((4 * (s.card : ℝ) * (C + s.card) + 6 * C) / p ^ 2 +
        ‖E - D‖ / p) / (1 / 12 : ℝ) ^ s.card :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = _ := by rw [one_div_pow, div_div_eq_mul_div, div_one]; ring

end

end Erdos4b
