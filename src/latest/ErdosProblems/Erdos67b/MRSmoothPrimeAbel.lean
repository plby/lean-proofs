import ErdosProblems.Erdos67b.MRSmoothPrimeWeight
import ErdosProblems.Erdos67b.LSeriesLogPhaseBridge

/-! # Explicit finite variation cost of the smooth prime weight -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

open LSeriesLogPhaseBridge

theorem mrNorm_weighted_sum_le_prefix_variation (u : ℕ → ℂ) (w : ℕ → ℝ)
    {A B : ℕ} (hAB : A ≤ B) {E : ℝ}
    (hprefix : ∀ m ∈ Finset.Icc A B, ‖∑ n ∈ Finset.Icc A m, u n‖ ≤ E) :
    ‖∑ n ∈ Finset.Icc A B, u n * (w n : ℂ)‖ ≤
      E * (|w B| + ∑ m ∈ Finset.Ico A B, |w m - w (m + 1)|) := by
  rw [sum_Icc_mul_eq_complexPartialSum u w hAB]
  calc
    _ ≤ ‖complexIntervalPartialSum u A B * (w B : ℂ)‖ +
        ‖∑ m ∈ Finset.Ico A B,
          complexIntervalPartialSum u A m * ((w m - w (m + 1) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ E * |w B| + ∑ m ∈ Finset.Ico A B, E * |w m - w (m + 1)| := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hprefix B (Finset.mem_Icc.2 ⟨hAB, le_rfl⟩))
          (abs_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact hprefix m (Finset.mem_Icc.2
          ⟨(Finset.mem_Ico.1 hm).1, (Finset.mem_Ico.1 hm).2.le⟩)
    _ = _ := by rw [← Finset.mul_sum, mul_add]

theorem mrPrimeWeightPolynomial_sub_le {x y : ℝ} (hxy : x ≤ y)
    (hx : 1 / 2 ≤ x) (hy : y ≤ 3) :
    |mrPrimeWeightPolynomial y - mrPrimeWeightPolynomial x| ≤ 64 * (y - x) := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun z (_hz : z ∈ Set.Icc x y) ↦ (hasDerivAt_mrPrimeWeightPolynomial z).hasDerivWithinAt)
    (fun z (hz : z ∈ Set.Ico x y) ↦ show ‖mrPrimeWeightPolynomialDeriv z‖ ≤ (64 : ℝ) by
      simpa only [Real.norm_eq_abs] using mrPrimeWeightPolynomialDeriv_abs_le
        (Set.mem_Icc.2 ⟨hx.trans hz.1, hz.2.le.trans hy⟩)) y (Set.mem_Icc.2 ⟨hxy, le_rfl⟩)
  simpa only [Real.norm_eq_abs] using hh

theorem mrSmoothPrimeWeight_variation_le {P q : ℝ} (hP : 0 < P) (hq : 0 < q)
    {A B : ℕ} (hAB : A ≤ B) (hlo : P / 2 ≤ q * A) (hhi : q * B ≤ 3 * P) :
    |mrPrimeWeightPolynomial (q * B / P)| +
      ∑ m ∈ Finset.Ico A B,
        |mrPrimeWeightPolynomial (q * m / P) -
          mrPrimeWeightPolynomial (q * (m + 1) / P)| ≤ 200 := by
  have hscaled {x : ℝ} (hx : x ∈ Set.Icc (A : ℝ) B) :
      q * x / P ∈ Set.Icc (1 / 2 : ℝ) 3 := by
    constructor
    · apply (le_div_iff₀ hP).2
      have hh := mul_le_mul_of_nonneg_left hx.1 hq.le
      linarith
    · apply (div_le_iff₀ hP).2
      exact (mul_le_mul_of_nonneg_left hx.2 hq.le).trans hhi
  have hABR : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hend := mrPrimeWeightPolynomial_abs_le (hscaled (Set.mem_Icc.2 ⟨hABR, le_rfl⟩))
  have hdiff (m : ℕ) (hm : m ∈ Finset.Ico A B) :
      |mrPrimeWeightPolynomial (q * m / P) -
        mrPrimeWeightPolynomial (q * (m + 1) / P)| ≤ 64 * q / P := by
    have hmA : (A : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ico.1 hm).1
    have hmB : (m : ℝ) + 1 ≤ B := by exact_mod_cast (Finset.mem_Ico.1 hm).2
    have hmUpper : (m : ℝ) ≤ B := by linarith
    have hmsLower : (A : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hm := hscaled (Set.mem_Icc.2 ⟨hmA, hmUpper⟩)
    have hms := hscaled (Set.mem_Icc.2 ⟨hmsLower, hmB⟩)
    rw [abs_sub_comm]
    apply (mrPrimeWeightPolynomial_sub_le (by gcongr; linarith) hm.1 hms.2).trans
    apply le_of_eq
    ring
  have hsum := Finset.sum_le_sum hdiff
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hAB] at hsum
  have hcost : ((B : ℝ) - A) * (64 * q / P) ≤ 160 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hP).2
    nlinarith
  linarith

theorem mrNorm_smoothPrime_weighted_sum_le {P q : ℝ} (hP : 0 < P) (hq : 0 < q)
    {A B : ℕ} (hAB : A ≤ B) (hlo : P / 2 ≤ q * A) (hhi : q * B ≤ 3 * P)
    (u : ℕ → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (hprefix : ∀ m ∈ Finset.Icc A B, ‖∑ n ∈ Finset.Icc A m, u n‖ ≤ E) :
    ‖∑ n ∈ Finset.Icc A B,
      u n * (mrPrimeWeightPolynomial (q * n / P) : ℂ)‖ ≤ 200 * E := by
  apply (mrNorm_weighted_sum_le_prefix_variation u
    (fun n ↦ mrPrimeWeightPolynomial (q * n / P)) hAB hprefix).trans
  calc
    _ ≤ E * 200 := by
      apply mul_le_mul_of_nonneg_left _ hE
      simpa only [Nat.cast_add, Nat.cast_one] using
        mrSmoothPrimeWeight_variation_le hP hq hAB hlo hhi
    _ = _ := mul_comm _ _

end

end Erdos67b
