import ErdosProblems.Erdos67b.MRPrimeMellinScale

/-! # Derivative bounds for the actual smooth prime-kernel integrand -/

namespace Erdos67b

noncomputable section

def mrSmoothPrimeKernelDerivative (P t x : ℝ) : ℂ :=
  ((mrPrimeWeightPolynomialDeriv (x / P) / P : ℝ) : ℂ) * mrPrimeMellinMonomial 0 t x +
    (mrPrimeWeightPolynomial (x / P) : ℂ) *
      (mrPrimeMellinCoefficient 0 t * (x : ℂ) ^ (mrPrimeMellinCoefficient 0 t - 1))

theorem hasDerivAt_mrPrimeMellinMonomial_zero (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (mrPrimeMellinMonomial 0 t)
      (mrPrimeMellinCoefficient 0 t * (x : ℂ) ^ (mrPrimeMellinCoefficient 0 t - 1)) x := by
  by_cases ht : t = 0
  · subst t
    have hf : mrPrimeMellinMonomial 0 0 = fun _ ↦ (1 : ℂ) := by
      funext y
      simp [mrPrimeMellinMonomial, mrPrimeMellinCoefficient]
    simpa only [hf, mrPrimeMellinCoefficient, Nat.cast_zero,
      Complex.ofReal_zero, zero_mul, zero_add] using hasDerivAt_const x (1 : ℂ)
  · have hz : mrPrimeMellinCoefficient 0 t ≠ 0 := by
      simp [mrPrimeMellinCoefficient, ht]
    simpa only [mrPrimeMellinMonomial] using! hasDerivAt_ofReal_cpow_const hx.ne' hz

theorem norm_mrPrimeMellinMonomial_zero_deriv (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖mrPrimeMellinCoefficient 0 t * (x : ℂ) ^ (mrPrimeMellinCoefficient 0 t - 1)‖ =
      |t| / x := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [mrPrimeMellinCoefficient, Complex.norm_real, Real.rpow_neg_one, div_eq_mul_inv]

theorem hasDerivAt_mrSmoothPrimeKernelIntegrand {P x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (mrSmoothPrimeKernelIntegrand P t) (mrSmoothPrimeKernelDerivative P t x) x := by
  have hp : HasDerivAt (fun y : ℝ ↦ mrPrimeWeightPolynomial (y / P))
      (mrPrimeWeightPolynomialDeriv (x / P) / P) x := by
    simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
      (hasDerivAt_mrPrimeWeightPolynomial (x / P)).comp x ((hasDerivAt_id x).div_const P)
  exact hp.ofReal_comp.mul (hasDerivAt_mrPrimeMellinMonomial_zero t hx)

theorem norm_mrSmoothPrimeKernelIntegrand_le {P x : ℝ} (hP : 0 < P)
    (hx : x ∈ Set.Icc (P / 2) (3 * P)) (t : ℝ) :
    ‖mrSmoothPrimeKernelIntegrand P t x‖ ≤ 40 := by
  have hxpos : 0 < x := by linarith [hx.1]
  have hu : x / P ∈ Set.Icc (1 / 2 : ℝ) 3 :=
    ⟨(le_div_iff₀ hP).2 (by linarith [hx.1]), (div_le_iff₀ hP).2 hx.2⟩
  rw [mrSmoothPrimeKernelIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_mrPrimeMellinMonomial 0 t hxpos, pow_zero, mul_one]
  exact mrPrimeWeightPolynomial_abs_le hu

theorem norm_mrSmoothPrimeKernelDerivative_le {P x : ℝ} (hP : 0 < P)
    (hx : x ∈ Set.Icc (P / 2) (3 * P)) (t : ℝ) :
    ‖mrSmoothPrimeKernelDerivative P t x‖ ≤ 80 * (1 + |t|) / P := by
  have hxpos : 0 < x := by linarith [hx.1]
  have hu : x / P ∈ Set.Icc (1 / 2 : ℝ) 3 :=
    ⟨(le_div_iff₀ hP).2 (by linarith [hx.1]), (div_le_iff₀ hP).2 hx.2⟩
  have hxinverse : 1 / x ≤ 2 / P :=
    (div_le_div_iff₀ hxpos hP).2 (by linarith [hx.1])
  have hfirst : |mrPrimeWeightPolynomialDeriv (x / P) / P| ≤ 64 / P := by
    rw [abs_div, abs_of_pos hP]
    exact div_le_div_of_nonneg_right (mrPrimeWeightPolynomialDeriv_abs_le hu) hP.le
  have hsecond : |mrPrimeWeightPolynomial (x / P)| * (|t| / x) ≤ 80 * |t| / P := by
    calc
      _ ≤ 40 * (|t| * (2 / P)) :=
        mul_le_mul (mrPrimeWeightPolynomial_abs_le hu)
          (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hxinverse (abs_nonneg t))
          (div_nonneg (abs_nonneg _) hxpos.le) (by norm_num)
      _ = _ := by ring
  unfold mrSmoothPrimeKernelDerivative
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, norm_mrPrimeMellinMonomial 0 t hxpos, pow_zero, mul_one,
    norm_mrPrimeMellinMonomial_zero_deriv t hxpos]
  calc
    _ ≤ 64 / P + 80 * |t| / P := add_le_add hfirst hsecond
    _ ≤ 80 * (1 + |t|) / P := by
      rw [← add_div]
      apply (div_le_div_iff_of_pos_right hP).2
      linarith

end

end Erdos67b
