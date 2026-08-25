import ErdosProblems.Erdos157.CharacterMomentBounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Differentiation of the convergent character Euler logarithmic series. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial Complex
open Filter Topology

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

noncomputable def eulerLogDerivative (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (p : PrimePolynomial K) (z : ℂ) : ℂ :=
  -(χ (AdjoinRoot.mk g p.1) * ((p.1.natDegree : ℂ) * z ^ (p.1.natDegree - 1))) /
    (1 - primeWeight g χ z p)

theorem hasDerivAt_log_eulerFactor (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (p : PrimePolynomial K) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    HasDerivAt (fun z => Complex.log (1 - primeWeight g χ z p))
      (eulerLogDerivative g χ p z) z := by
  have hslit : 1 - primeWeight g χ z p ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg, norm_neg] using
      Complex.mem_slitPlane_of_norm_lt_one
        (z := -primeWeight g χ z p) (by
          simpa only [norm_neg] using primeWeight_norm_lt_one g hg χ z hz p)
  exact (((hasDerivAt_pow p.1.natDegree z).const_mul
    (χ (AdjoinRoot.mk g p.1))).const_sub 1).clog hslit

/-- Uniform derivative control on any smaller closed disk. -/
theorem norm_eulerLogDerivative_le (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (p : PrimePolynomial K)
    (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖eulerLogDerivative g χ p z‖ ≤ 2 * (p.1.natDegree : ℝ) * r ^ (p.1.natDegree - 1) := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  have htwo : (2 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast Fintype.one_lt_card (α := K)
  have hhalf : r < 1 / 2 := by
    have := mul_le_mul_of_nonneg_right htwo hr.le
    nlinarith
  have hrone : r ≤ 1 := by linarith
  have hweight : ‖primeWeight g χ z p‖ ≤ r := by
    calc
      _ ≤ ‖z‖ ^ p.1.natDegree := by
        rw [primeWeight, norm_mul, norm_pow]
        exact mul_le_of_le_one_left (by positivity) (character_norm_le_one χ _)
      _ ≤ r ^ p.1.natDegree := pow_le_pow_left₀ (norm_nonneg _) hz _
      _ ≤ r := by
        have hp : 1 ≤ p.1.natDegree := primePolynomial_degree_pos p
        simpa only [pow_one] using pow_le_pow_of_le_one hr.le hrone hp
  have hden : (1 / 2 : ℝ) ≤ ‖1 - primeWeight g χ z p‖ := by
    have htriangle := norm_sub_norm_le (1 : ℂ) (primeWeight g χ z p)
    simp only [norm_one] at htriangle
    linarith
  have hnum : ‖-(χ (AdjoinRoot.mk g p.1) *
      ((p.1.natDegree : ℂ) * z ^ (p.1.natDegree - 1)))‖ ≤
      (p.1.natDegree : ℝ) * r ^ (p.1.natDegree - 1) := by
    simp only [norm_neg, norm_mul, Complex.norm_natCast, norm_pow]
    calc
      _ ≤ 1 * ((p.1.natDegree : ℝ) * r ^ (p.1.natDegree - 1)) := by
        apply mul_le_mul (character_norm_le_one χ _)
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity)
        · positivity
        · positivity
      _ = _ := one_mul _
  rw [eulerLogDerivative, norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 - primeWeight g χ z p‖)).mpr
  have hmul := mul_le_mul_of_nonneg_left hden
    (by positivity : 0 ≤ 2 * (p.1.natDegree : ℝ) * r ^ (p.1.natDegree - 1))
  nlinarith

noncomputable def logEulerSeries (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ) (z : ℂ) : ℂ :=
  ∑' p : PrimePolynomial K, Complex.log (1 - primeWeight g χ z p)

theorem summable_eulerLogDerivative (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (z : ℂ) (hz : ‖z‖ ≤ r) :
    Summable (fun p : PrimePolynomial K => eulerLogDerivative g χ p z) := by
  apply ((summable_prime_derivative_weight (K := K) r hr hqr).mul_left 2).of_norm_bounded
  intro p
  simpa only [mul_assoc] using norm_eulerLogDerivative_le g hg χ r hr hqr p z hz

/-- The logarithmic Euler series may be differentiated throughout every smaller disk. -/
theorem hasDerivAt_logEulerSeries (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (z : ℂ) (hz : ‖z‖ < r) :
    HasDerivAt (logEulerSeries g χ)
      (∑' p : PrimePolynomial K, eulerLogDerivative g χ p z) z := by
  have hs : Summable (fun p : PrimePolynomial K =>
      2 * (p.1.natDegree : ℝ) * r ^ (p.1.natDegree - 1)) := by
    simpa only [mul_assoc] using (summable_prime_derivative_weight (K := K) r hr hqr).mul_left 2
  apply hasDerivAt_tsum_of_isPreconnected hs Metric.isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
    (y₀ := (0 : ℂ))
  · intro p y hy
    apply hasDerivAt_log_eulerFactor g hg χ p y
    have hynorm : ‖y‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    exact (mul_le_mul_of_nonneg_left hynorm.le (by positivity)).trans_lt hqr
  · intro p y hy
    apply norm_eulerLogDerivative_le g hg χ r hr hqr p y
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using hy : ‖y‖ < r).le
  · simpa only [Metric.mem_ball, dist_self] using hr
  · exact summable_log_eulerFactor g hg χ 0 (by simp)
  · simpa only [Metric.mem_ball, dist_zero_right] using hz

/-- The polynomial logarithmic derivative is the negative sum of Euler-factor derivatives. -/
theorem lPolynomial_logDerivative_eq (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (z : ℂ) (hz : ‖z‖ < r) :
    (lPolynomial g χ).derivative.eval z / (lPolynomial g χ).eval z =
      -(∑' p : PrimePolynomial K, eulerLogDerivative g χ p z) := by
  have hsmall : (Fintype.card K : ℝ) * ‖z‖ < 1 :=
    (mul_le_mul_of_nonneg_left hz.le (by positivity)).trans_lt hqr
  have hlog := hasDerivAt_logEulerSeries g hg χ r hr hqr z hz
  have hpoly := (lPolynomial g χ).hasDerivAt z
  have hproduct := hlog.cexp.mul hpoly
  have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 z :=
    Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have heq : (fun w => Complex.exp (logEulerSeries g χ w) * (lPolynomial g χ).eval w) =ᶠ[𝓝 z]
      (fun _ => (1 : ℂ)) := by
    filter_upwards [hball] with w hw
    have hwnorm : ‖w‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    have hwsmall : (Fintype.card K : ℝ) * ‖w‖ < 1 :=
      (mul_le_mul_of_nonneg_left hwnorm.le (by positivity)).trans_lt hqr
    rw [logEulerSeries, exp_sum_log_eq_inv_lPolynomial g hg χ hχ w hwsmall]
    exact inv_mul_cancel₀ (lPolynomial_eval_ne_zero g hg χ hχ w hwsmall)
  have hzero := hproduct.unique ((hasDerivAt_const z (1 : ℂ)).congr_of_eventuallyEq heq)
  have hfactor : Complex.exp (logEulerSeries g χ z) *
      ((∑' p : PrimePolynomial K, eulerLogDerivative g χ p z) * (lPolynomial g χ).eval z +
        (lPolynomial g χ).derivative.eval z) = 0 := by
    linear_combination hzero
  have hinside := (mul_eq_zero.mp hfactor).resolve_left (Complex.exp_ne_zero _)
  apply (div_eq_iff (lPolynomial_eval_ne_zero g hg χ hχ z hsmall)).mpr
  linear_combination hinside

end Erdos157.Elementary.PolynomialCharacters
