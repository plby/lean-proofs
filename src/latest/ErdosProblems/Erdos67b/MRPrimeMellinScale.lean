import ErdosProblems.Erdos67b.MRPrimeMellinKernel

/-! # Exact positive scaling of the prime Mellin integral -/

namespace Erdos67b

noncomputable section

def mrSmoothPrimeKernelIntegrand (P t x : ℝ) : ℂ :=
  (mrPrimeWeightPolynomial (x / P) : ℂ) * mrPrimeMellinMonomial 0 t x

def mrScaledPrimeMellinIntegral (P t : ℝ) : ℂ :=
  ∫ x in P / 2..3 * P, mrSmoothPrimeKernelIntegrand P t x

theorem mrPrimeMellinMonomial_mul (k : ℕ) (t : ℝ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    mrPrimeMellinMonomial k t (x * y) =
      mrPrimeMellinMonomial k t x * mrPrimeMellinMonomial k t y := by
  simpa only [mrPrimeMellinMonomial, Complex.ofReal_mul] using
    Complex.mul_cpow_ofReal_nonneg hx.le hy.le (mrPrimeMellinCoefficient k t)

theorem mrScaledPrimeMellinIntegral_eq {P : ℝ} (hP : 0 < P) (t : ℝ) :
    mrScaledPrimeMellinIntegral P t =
      (P : ℂ) * mrPrimeMellinMonomial 0 t P * mrPrimeMellinKernel t := by
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (f := mrSmoothPrimeKernelIntegrand P t) (a := (1 / 2 : ℝ)) (b := 3) P
  have hpoint : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 3,
      mrSmoothPrimeKernelIntegrand P t (P * x) =
        mrPrimeMellinMonomial 0 t P *
          ((mrPrimeWeightPolynomial x : ℂ) * mrPrimeMellinMonomial 0 t x) := by
    intro x hx
    have hx' : x ∈ Set.Icc (1 / 2 : ℝ) 3 := by
      simpa only [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3)] using hx
    have hxpos : 0 < x := by linarith [hx'.1]
    rw [mrSmoothPrimeKernelIntegrand, mul_div_cancel_left₀ x hP.ne',
      mrPrimeMellinMonomial_mul 0 t hP hxpos]
    ring
  have hint : (∫ x in (1 / 2 : ℝ)..3, mrSmoothPrimeKernelIntegrand P t (P * x)) =
      mrPrimeMellinMonomial 0 t P * mrPrimeMellinKernel t := by
    rw [mrPrimeMellinKernel, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr hpoint
  rw [hint] at hsub
  have hleft : P * (1 / 2 : ℝ) = P / 2 := by ring
  have hright : P * 3 = 3 * P := mul_comm _ _
  rw [hleft, hright] at hsub
  change P • (mrPrimeMellinMonomial 0 t P * mrPrimeMellinKernel t) =
    mrScaledPrimeMellinIntegral P t at hsub
  rw [← hsub, Complex.real_smul]
  ring

theorem norm_mrScaledPrimeMellinIntegral_le {P : ℝ} (hP : 0 < P) (t : ℝ) :
    ‖mrScaledPrimeMellinIntegral P t‖ ≤ 2000 * P / (1 + t ^ 2) := by
  rw [mrScaledPrimeMellinIntegral_eq hP, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hP,
    norm_mrPrimeMellinMonomial 0 t hP, pow_zero, mul_one]
  calc
    _ ≤ P * (2000 / (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left (norm_mrPrimeMellinKernel_le t) hP.le
    _ = _ := by ring

end

end Erdos67b
