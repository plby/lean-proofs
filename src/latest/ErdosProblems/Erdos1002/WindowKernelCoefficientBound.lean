import ErdosProblems.Erdos1002.WindowKernelEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative decay of the nearest-cell window coefficient

This file supplies the analytic input left open by the finite arithmetic
reduction.  The coefficient is the exact sine-integral expression from the
manuscript.  We prove both a uniform bound and the reciprocal tail bound from
the already formalized Dirichlet integral estimate, including negative and
zero frequencies.  The final squared estimate is stated with precisely the
`windowDecayWeight` used by `WindowKernelEnvelope`.
-/

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Erdos1002

noncomputable section

theorem paperSineIntegral_neg (x : ℝ) :
    paperSineIntegral (-x) = -paperSineIntegral x := by
  unfold paperSineIntegral
  calc
    (∫ t in (0 : ℝ)..-x, Real.sinc t) =
        ∫ t in x..(0 : ℝ), Real.sinc (-t) := by
      simpa only [neg_zero] using!
        (intervalIntegral.integral_comp_neg (fun t : ℝ ↦ Real.sinc t)
          (a := x) (b := 0)).symm
    _ = ∫ t in x..(0 : ℝ), Real.sinc t := by
      apply intervalIntegral.integral_congr
      intro t _ht
      exact Real.sinc_neg t
    _ = -(∫ t in (0 : ℝ)..x, Real.sinc t) :=
      intervalIntegral.integral_symm 0 x

theorem abs_paperSineIntegral_le_abs (x : ℝ) :
    |paperSineIntegral x| ≤ |x| := by
  unfold paperSineIntegral
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := x) (C := (1 : ℝ))
    (f := fun t : ℝ ↦ Real.sinc t) (fun t _ht ↦ by
      simpa only [Real.norm_eq_abs] using! Real.abs_sinc_le_one t)
  simpa only [Real.norm_eq_abs, one_mul, sub_zero] using! h

theorem abs_pi_half_sub_paperSineIntegral_le
    {x : ℝ} (hx : 0 < x) :
    |Real.pi / 2 - paperSineIntegral x| ≤ 3 * x⁻¹ := by
  have h := abs_dirichletSineLimit_sub_sineIntegralTruncation_le
    (1 : ℝ) x (by norm_num) hx
  simpa only [dirichletSineLimit_one, sineIntegralTruncation_one,
    paperSineIntegral, abs_one, inv_one, one_mul] using! h

theorem windowKernelCoefficient_neg (d : ℕ) (m : ℤ) :
    windowKernelCoefficient d (-m) = -windowKernelCoefficient d m := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hneg : -m ≠ 0 := neg_ne_zero.mpr hm
    simp only [windowKernelCoefficient, if_neg hm, if_neg hneg, Int.sign_neg]
    have harg :
        Real.pi * ((-m : ℤ) : ℝ) / (d : ℝ) =
          -(Real.pi * (m : ℝ) / (d : ℝ)) := by
      push_cast
      ring
    rw [harg, paperSineIntegral_neg]
    push_cast
    ring

theorem norm_windowKernelCoefficient_le_twelve_of_abs_le
    {d : ℕ} (hd : 0 < d) (m : ℤ)
    (hcentral : |(m : ℝ)| ≤ (d : ℝ)) :
    ‖windowKernelCoefficient d m‖ ≤ 12 := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hsign : |((Int.sign m : ℤ) : ℝ)| ≤ 1 := by
      have hsignInt : |Int.sign m| = (1 : ℤ) :=
        Int.abs_sign_of_ne_zero hm
      exact_mod_cast hsignInt.le
    have harg :
        |Real.pi * (m : ℝ) / (d : ℝ)| =
          Real.pi * |(m : ℝ)| / (d : ℝ) := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_pos (by exact_mod_cast hd : (0 : ℝ) < d)]
    rw [windowKernelCoefficient, if_neg hm]
    calc
      ‖Complex.I * (Real.pi * (Int.sign m : ℝ)) -
          (2 * Complex.I) *
            (paperSineIntegral (Real.pi * (m : ℝ) / (d : ℝ)) : ℂ)‖ ≤
          ‖Complex.I * (Real.pi * (Int.sign m : ℝ))‖ +
            ‖(2 * Complex.I) *
              (paperSineIntegral (Real.pi * (m : ℝ) / (d : ℝ)) : ℂ)‖ :=
        norm_sub_le _ _
      _ = |Real.pi * ((Int.sign m : ℤ) : ℝ)| +
          2 * |paperSineIntegral
            (Real.pi * (m : ℝ) / (d : ℝ))| := by
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, mul_one]
        norm_num
      _ ≤ Real.pi +
          2 * |Real.pi * (m : ℝ) / (d : ℝ)| := by
        apply add_le_add
        · rw [abs_mul, abs_of_pos Real.pi_pos]
          simpa only [mul_one] using!
            mul_le_mul_of_nonneg_left hsign Real.pi_pos.le
        · exact mul_le_mul_of_nonneg_left
            (abs_paperSineIntegral_le_abs _) (by norm_num)
      _ = Real.pi + 2 * (Real.pi * |(m : ℝ)| / (d : ℝ)) := by rw [harg]
      _ ≤ 12 := by
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd
        have hratio : Real.pi * |(m : ℝ)| / (d : ℝ) ≤ Real.pi := by
          apply (div_le_iff₀ hdR).2
          nlinarith [Real.pi_pos]
        nlinarith [Real.pi_lt_four]

theorem norm_windowKernelCoefficient_eq_two_mul_tail_of_pos
    {d : ℕ} {m : ℤ} (hm : 0 < m) :
    ‖windowKernelCoefficient d m‖ =
      2 * |Real.pi / 2 -
        paperSineIntegral (Real.pi * (m : ℝ) / (d : ℝ))| := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hsign : Int.sign m = 1 := Int.sign_eq_one_iff_pos.mpr hm
  rw [windowKernelCoefficient, if_neg hm0, hsign]
  have heq :
      Complex.I * (Real.pi * ((1 : ℤ) : ℝ)) -
          (2 * Complex.I) *
            (paperSineIntegral (Real.pi * (m : ℝ) / (d : ℝ)) : ℂ) =
        (2 * Complex.I) *
          ((Real.pi / 2 -
            paperSineIntegral (Real.pi * (m : ℝ) / (d : ℝ)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem norm_windowKernelCoefficient_le_six_mul_div_of_pos
    {d : ℕ} (hd : 0 < d) {m : ℤ} (hm : 0 < m) :
    ‖windowKernelCoefficient d m‖ ≤
      6 * (d : ℝ) / (m : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  let x : ℝ := Real.pi * (m : ℝ) / (d : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have htail := abs_pi_half_sub_paperSineIntegral_le hx
  have hratioPos : 0 < (m : ℝ) / (d : ℝ) := div_pos hmR hdR
  have hbase : (m : ℝ) / (d : ℝ) ≤ x := by
    dsimp [x]
    have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc
      (m : ℝ) / (d : ℝ) = 1 * ((m : ℝ) / (d : ℝ)) := by ring
      _ ≤ Real.pi * ((m : ℝ) / (d : ℝ)) :=
        mul_le_mul_of_nonneg_right hpi hratioPos.le
      _ = Real.pi * (m : ℝ) / (d : ℝ) := by ring
  have hinv : x⁻¹ ≤ ((m : ℝ) / (d : ℝ))⁻¹ :=
    (inv_le_inv₀ hx hratioPos).2 hbase
  have hinvEq : ((m : ℝ) / (d : ℝ))⁻¹ =
      (d : ℝ) / (m : ℝ) := by
    field_simp [hdR.ne', hmR.ne']
  rw [norm_windowKernelCoefficient_eq_two_mul_tail_of_pos hm]
  calc
    2 * |Real.pi / 2 - paperSineIntegral x| ≤
        2 * (3 * x⁻¹) := mul_le_mul_of_nonneg_left htail (by norm_num)
    _ ≤ 2 * (3 * (((m : ℝ) / (d : ℝ))⁻¹)) := by
      gcongr
    _ = 6 * (d : ℝ) / (m : ℝ) := by
      rw [hinvEq]
      ring

theorem norm_windowKernelCoefficient_le_six_mul_div_abs
    {d : ℕ} (hd : 0 < d) {m : ℤ} (hm : m ≠ 0) :
    ‖windowKernelCoefficient d m‖ ≤
      6 * (d : ℝ) / |(m : ℝ)| := by
  by_cases hmPos : 0 < m
  · have h := norm_windowKernelCoefficient_le_six_mul_div_of_pos hd hmPos
    simpa [abs_of_pos (by exact_mod_cast hmPos : (0 : ℝ) < (m : ℝ))] using! h
  · have hmNeg : m < 0 := lt_of_le_of_ne (le_of_not_gt hmPos) hm
    have hkPos : 0 < -m := neg_pos.mpr hmNeg
    have h := norm_windowKernelCoefficient_le_six_mul_div_of_pos
      hd hkPos
    rw [windowKernelCoefficient_neg] at h
    have habs : ((-m : ℤ) : ℝ) = |(m : ℝ)| := by
      push_cast
      rw [abs_of_neg (by exact_mod_cast hmNeg : (m : ℝ) < 0)]
    simpa only [norm_neg, habs] using! h

theorem abs_int_natCast_sub_eq_natDist (m M : ℕ) :
    |(m : ℝ) - (M : ℝ)| = (Nat.dist m M : ℝ) := by
  by_cases hmM : m ≤ M
  · rw [Nat.dist_eq_sub_of_le hmM]
    rw [abs_of_nonpos]
    · rw [Nat.cast_sub hmM]
      ring
    · exact sub_nonpos.mpr (by exact_mod_cast hmM)
  · have hMm : M ≤ m := Nat.le_of_not_ge hmM
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hMm]
    rw [abs_of_nonneg]
    · rw [Nat.cast_sub hMm]
    · exact sub_nonneg.mpr (by exact_mod_cast hMm)

/-- Squared coefficient decay in exactly the natural-distance coordinates
used by `WindowKernelEnvelope`. -/
theorem norm_sq_windowKernelCoefficient_nat_sub_le
    (d m M : ℕ) (hd : 0 < d) :
    ‖windowKernelCoefficient d ((m : ℤ) - (M : ℤ))‖ ^ 2 ≤
      144 * windowDecayWeight d m M := by
  by_cases hcentral : Nat.dist m M ≤ d
  · have hcentralR :
        |(m : ℝ) - (M : ℝ)| ≤ (d : ℝ) := by
      rw [abs_int_natCast_sub_eq_natDist]
      exact_mod_cast hcentral
    have h12 := norm_windowKernelCoefficient_le_twelve_of_abs_le
      hd ((m : ℤ) - (M : ℤ)) (by
        simpa only [Int.cast_sub, Int.cast_natCast] using! hcentralR)
    calc
      ‖windowKernelCoefficient d ((m : ℤ) - (M : ℤ))‖ ^ 2 ≤ 12 ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h12 2
      _ = 144 * windowDecayWeight d m M := by
        norm_num [windowDecayWeight, hcentral]
  · have hdist : d < Nat.dist m M := Nat.lt_of_not_ge hcentral
    have hdistPos : 0 < Nat.dist m M :=
      lt_of_le_of_lt (Nat.zero_le d) hdist
    have hne : (m : ℤ) - (M : ℤ) ≠ 0 := by
      intro hzero
      have heq : m = M := by
        exact_mod_cast sub_eq_zero.mp hzero
      rw [heq, Nat.dist_self] at hdistPos
      exact (Nat.lt_asymm hdistPos hdistPos).elim
    have h6 := norm_windowKernelCoefficient_le_six_mul_div_abs hd hne
    have h12tail :
        ‖windowKernelCoefficient d ((m : ℤ) - (M : ℤ))‖ ≤
          12 * (d : ℝ) / |(m : ℝ) - (M : ℝ)| := by
      calc
        ‖windowKernelCoefficient d ((m : ℤ) - (M : ℤ))‖ ≤
            6 * (d : ℝ) / |(m : ℝ) - (M : ℝ)| := by
          simpa only [Int.cast_sub, Int.cast_natCast] using! h6
        _ ≤ 12 * (d : ℝ) / |(m : ℝ) - (M : ℝ)| := by
          exact div_le_div_of_nonneg_right
            (show 6 * (d : ℝ) ≤ 12 * (d : ℝ) by
              exact mul_le_mul_of_nonneg_right (by norm_num)
                (show (0 : ℝ) ≤ (d : ℝ) by positivity))
            (abs_nonneg ((m : ℝ) - (M : ℝ)))
    calc
      ‖windowKernelCoefficient d ((m : ℤ) - (M : ℤ))‖ ^ 2 ≤
          (12 * (d : ℝ) /
            |(m : ℝ) - (M : ℝ)|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h12tail 2
      _ = 144 * ((d : ℝ) ^ 2 / (Nat.dist m M : ℝ) ^ 2) := by
        rw [abs_int_natCast_sub_eq_natDist]
        ring
      _ = 144 * windowDecayWeight d m M := by
        simp [windowDecayWeight, hcentral]

end

end Erdos1002
