import ErdosProblems.Erdos67b.MRSmoothPrimeWeight
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Quadratic frequency decay of the polynomial Mellin kernel

Two exact integrations by parts use the double endpoint zeros. The
coefficients have positive real part, so the proof includes frequency zero.
-/

open MeasureTheory

namespace Erdos67b

noncomputable section

def mrPrimeMellinCoefficient (k : ℕ) (t : ℝ) : ℂ := (k : ℂ) + (t : ℂ) * Complex.I

def mrPrimeMellinMonomial (k : ℕ) (t x : ℝ) : ℂ :=
  (x : ℂ) ^ mrPrimeMellinCoefficient k t

def mrPrimeMellinKernel (t : ℝ) : ℂ :=
  ∫ x in (1 / 2 : ℝ)..3, (mrPrimeWeightPolynomial x : ℂ) * mrPrimeMellinMonomial 0 t x

theorem mrPrimeMellinCoefficient_succ_ne_zero (k : ℕ) (t : ℝ) :
    mrPrimeMellinCoefficient (k + 1) t ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  simp [mrPrimeMellinCoefficient] at hr
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem hasDerivAt_mrPrimeMellinMonomial (k : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (mrPrimeMellinMonomial (k + 1) t)
      (mrPrimeMellinCoefficient (k + 1) t * mrPrimeMellinMonomial k t x) x := by
  have hsub : mrPrimeMellinCoefficient (k + 1) t - 1 = mrPrimeMellinCoefficient k t := by
    simp only [mrPrimeMellinCoefficient, Nat.cast_add, Nat.cast_one]
    ring
  simpa only [mrPrimeMellinMonomial, hsub] using!
    hasDerivAt_ofReal_cpow_const hx.ne' (mrPrimeMellinCoefficient_succ_ne_zero k t)

theorem continuousOn_mrPrimeMellinMonomial (k : ℕ) (t : ℝ) :
    ContinuousOn (mrPrimeMellinMonomial k t) (Set.Icc (1 / 2 : ℝ) 3) := by
  intro x hx
  exact (Complex.continuousAt_ofReal_cpow_const x (mrPrimeMellinCoefficient k t)
    (Or.inr (show x ≠ 0 by linarith [hx.1]))).continuousWithinAt

theorem norm_mrPrimeMellinMonomial (k : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖mrPrimeMellinMonomial k t x‖ = x ^ k := by
  rw [mrPrimeMellinMonomial, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [mrPrimeMellinCoefficient]

theorem mrPrimeMellinCoefficient_norm_sq (k : ℕ) (t : ℝ) :
    ‖mrPrimeMellinCoefficient k t‖ ^ 2 = (k : ℝ) ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm]
  simp [mrPrimeMellinCoefficient, Complex.normSq_apply, pow_two]

theorem mrPrimeMellinCoefficient_product_norm_lower (t : ℝ) :
    1 + t ^ 2 ≤ ‖mrPrimeMellinCoefficient 1 t‖ * ‖mrPrimeMellinCoefficient 2 t‖ := by
  have h1 := mrPrimeMellinCoefficient_norm_sq 1 t
  have h2 := mrPrimeMellinCoefficient_norm_sq 2 t
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_pow] at h1 h2
  have hn1 := norm_nonneg (mrPrimeMellinCoefficient 1 t)
  have hn2 := norm_nonneg (mrPrimeMellinCoefficient 2 t)
  have hle : ‖mrPrimeMellinCoefficient 1 t‖ ≤ ‖mrPrimeMellinCoefficient 2 t‖ := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hle hn1
  nlinarith

theorem mrPrimeMellin_integrateByParts (k : ℕ) (t : ℝ) (f f' : ℝ → ℝ)
    (hderiv : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 3, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Set.Icc (1 / 2 : ℝ) 3))
    (hzeroLeft : f (1 / 2) = 0) (hzeroRight : f 3 = 0) :
    mrPrimeMellinCoefficient (k + 1) t *
        (∫ x in (1 / 2 : ℝ)..3, (f x : ℂ) * mrPrimeMellinMonomial k t x) =
      -(∫ x in (1 / 2 : ℝ)..3, (f' x : ℂ) * mrPrimeMellinMonomial (k + 1) t x) := by
  have horder : (1 / 2 : ℝ) ≤ 3 := by norm_num
  have hmem {x : ℝ} (hx : x ∈ Set.uIcc (1 / 2 : ℝ) 3) :
      x ∈ Set.Icc (1 / 2 : ℝ) 3 := by simpa only [Set.uIcc_of_le horder] using hx
  have huc : ContinuousOn (fun x ↦ (f' x : ℂ)) (Set.Icc (1 / 2 : ℝ) 3) :=
    Complex.continuous_ofReal.comp_continuousOn hcont
  have hvc : ContinuousOn
      (fun x ↦ mrPrimeMellinCoefficient (k + 1) t * mrPrimeMellinMonomial k t x)
      (Set.Icc (1 / 2 : ℝ) 3) :=
    continuousOn_const.mul (continuousOn_mrPrimeMellinMonomial k t)
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x ↦ (f x : ℂ)) (u' := fun x ↦ (f' x : ℂ))
    (v := mrPrimeMellinMonomial (k + 1) t)
    (v' := fun x ↦ mrPrimeMellinCoefficient (k + 1) t * mrPrimeMellinMonomial k t x)
    (a := (1 / 2 : ℝ)) (b := 3)
    (fun x hx ↦ (hderiv x (hmem hx)).ofReal_comp)
    (fun x hx ↦ hasDerivAt_mrPrimeMellinMonomial k t (by linarith [(hmem hx).1]))
    (huc.intervalIntegrable_of_Icc horder) (hvc.intervalIntegrable_of_Icc horder)
  have hleft : (∫ x in (1 / 2 : ℝ)..3,
      (f x : ℂ) * (mrPrimeMellinCoefficient (k + 1) t * mrPrimeMellinMonomial k t x)) =
      mrPrimeMellinCoefficient (k + 1) t *
        (∫ x in (1 / 2 : ℝ)..3, (f x : ℂ) * mrPrimeMellinMonomial k t x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hleft] at hh
  simpa only [hzeroLeft, hzeroRight, Complex.ofReal_zero, zero_mul, sub_self, zero_sub] using hh

theorem mrPrimeMellinKernel_secondDerivative_identity (t : ℝ) :
    mrPrimeMellinCoefficient 1 t * mrPrimeMellinCoefficient 2 t * mrPrimeMellinKernel t =
      ∫ x in (1 / 2 : ℝ)..3,
        (mrPrimeWeightPolynomialDerivTwo x : ℂ) * mrPrimeMellinMonomial 2 t x := by
  obtain ⟨h0, h3, h0', h3'⟩ := mrPrimeWeightPolynomial_endpoints
  have h1 := mrPrimeMellin_integrateByParts 0 t mrPrimeWeightPolynomial mrPrimeWeightPolynomialDeriv
    (fun x _hx ↦ hasDerivAt_mrPrimeWeightPolynomial x)
    continuous_mrPrimeWeightPolynomialDeriv.continuousOn h0 h3
  have h2 := mrPrimeMellin_integrateByParts 1 t mrPrimeWeightPolynomialDeriv
    mrPrimeWeightPolynomialDerivTwo (fun x _hx ↦ hasDerivAt_mrPrimeWeightPolynomialDeriv x)
    continuous_mrPrimeWeightPolynomialDerivTwo.continuousOn h0' h3'
  change mrPrimeMellinCoefficient 1 t * mrPrimeMellinKernel t = _ at h1
  calc
    _ = mrPrimeMellinCoefficient 2 t *
        (mrPrimeMellinCoefficient 1 t * mrPrimeMellinKernel t) := by ring
    _ = mrPrimeMellinCoefficient 2 t *
        (-(∫ x in (1 / 2 : ℝ)..3,
          (mrPrimeWeightPolynomialDeriv x : ℂ) * mrPrimeMellinMonomial 1 t x)) := by rw [h1]
    _ = -(mrPrimeMellinCoefficient 2 t *
        (∫ x in (1 / 2 : ℝ)..3,
          (mrPrimeWeightPolynomialDeriv x : ℂ) * mrPrimeMellinMonomial 1 t x)) := by ring
    _ = _ := by rw [h2, neg_neg]

theorem mrPrimeMellin_secondDerivative_integral_norm_le (t : ℝ) :
    ‖∫ x in (1 / 2 : ℝ)..3,
      (mrPrimeWeightPolynomialDerivTwo x : ℂ) * mrPrimeMellinMonomial 2 t x‖ ≤ 2000 := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := 3) (C := 675)
    (f := fun x ↦ (mrPrimeWeightPolynomialDerivTwo x : ℂ) * mrPrimeMellinMonomial 2 t x)
    (by
      intro x hx
      have hx' : x ∈ Set.Ioc (1 / 2 : ℝ) 3 := by
        simpa only [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3)] using hx
      have hxI : x ∈ Set.Icc (1 / 2 : ℝ) 3 := ⟨hx'.1.le, hx'.2⟩
      have hxpos : 0 < x := by linarith [hx'.1]
      have hxsq : x ^ 2 ≤ (9 : ℝ) := by nlinarith [hx'.2]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mrPrimeMellinMonomial 2 t hxpos]
      calc
        _ ≤ (75 : ℝ) * 9 := mul_le_mul (mrPrimeWeightPolynomialDerivTwo_abs_le hxI)
          hxsq (sq_nonneg x) (by norm_num)
        _ = _ := by norm_num)
  norm_num at hh
  linarith

theorem norm_mrPrimeMellinKernel_le (t : ℝ) :
    ‖mrPrimeMellinKernel t‖ ≤ 2000 / (1 + t ^ 2) := by
  have hprod : ‖mrPrimeMellinCoefficient 1 t‖ * ‖mrPrimeMellinCoefficient 2 t‖ *
      ‖mrPrimeMellinKernel t‖ ≤ 2000 := by
    calc
      _ = ‖mrPrimeMellinCoefficient 1 t * mrPrimeMellinCoefficient 2 t *
          mrPrimeMellinKernel t‖ := by rw [norm_mul, norm_mul]
      _ = ‖∫ x in (1 / 2 : ℝ)..3,
          (mrPrimeWeightPolynomialDerivTwo x : ℂ) * mrPrimeMellinMonomial 2 t x‖ := by
        rw [mrPrimeMellinKernel_secondDerivative_identity]
      _ ≤ 2000 := mrPrimeMellin_secondDerivative_integral_norm_le t
  have hh := mul_le_mul_of_nonneg_right (mrPrimeMellinCoefficient_product_norm_lower t)
    (norm_nonneg (mrPrimeMellinKernel t))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)).2
  nlinarith

end

end Erdos67b
