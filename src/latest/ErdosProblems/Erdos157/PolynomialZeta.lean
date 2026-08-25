import ErdosProblems.Erdos157.CharacterLogDerivative

/-! The elementary zeta series of the polynomial ring. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial
open Filter Topology

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

omit [DecidableEq K] [Fintype K] in
theorem trivial_modulus_character (f : K[X]) :
    (1 : MulChar (AdjoinRoot (1 : K[X])) ℂ) (AdjoinRoot.mk 1 f) = 1 := by
  have heq : AdjoinRoot.mk (1 : K[X]) f = 1 := by
    rw [← map_one (AdjoinRoot.mk (1 : K[X])), AdjoinRoot.mk_eq_mk]
    exact one_dvd _
  rw [heq, map_one]

theorem zeta_coefficient (d : ℕ) :
    coefficient (1 : K[X]) 1 d = (Fintype.card K : ℂ) ^ d := by
  simp [coefficient, trivial_modulus_character, card_monic]

theorem polynomial_zeta_series (z : ℂ) (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    (∑' f : AllMonic K, monicTerm 1 1 z f) = (1 - (Fintype.card K : ℂ) * z)⁻¹ := by
  have hs := (summable_norm_monicTerm (1 : K[X]) monic_one 1 z hz).of_norm
  rw [hs.tsum_sigma]
  have hin : ∀ d, (∑' f : MonicDegreeEq K d, monicTerm 1 1 z ⟨d, f⟩) =
      ((Fintype.card K : ℂ) * z) ^ d := by
    intro d
    rw [tsum_fintype]
    simp [monicTerm, trivial_modulus_character, card_monic, mul_pow]
  simp_rw [hin]
  exact (hasSum_geometric_of_norm_lt_one (by
    simpa only [norm_mul, Complex.norm_natCast] using hz)).tsum_eq

theorem exp_logEulerSeries_zeta (z : ℂ) (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    Complex.exp (logEulerSeries (1 : K[X]) 1 z) = 1 - (Fintype.card K : ℂ) * z := by
  have heuler := eulerProduct_mul_monicSeries (1 : K[X]) monic_one 1 z hz
  rw [polynomial_zeta_series z hz] at heuler
  rw [logEulerSeries, Complex.cexp_tsum_eq_tprod
    (eulerFactor_ne_zero (1 : K[X]) monic_one 1 z hz)
    (summable_log_eulerFactor (1 : K[X]) monic_one 1 z hz)]
  have hne : 1 - (Fintype.card K : ℂ) * z ≠ 0 := by
    intro h
    have heq : (Fintype.card K : ℂ) * z = 1 := (sub_eq_zero.mp h).symm
    have hn : ‖(Fintype.card K : ℂ) * z‖ < 1 := by
      simpa only [norm_mul, Complex.norm_natCast] using hz
    simp [heq] at hn
  calc
    _ = ((∏' p : PrimePolynomial K, (1 - primeWeight 1 1 z p)) *
          (1 - (Fintype.card K : ℂ) * z)⁻¹) * (1 - (Fintype.card K : ℂ) * z) := by
      rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
    _ = _ := by rw [heuler, one_mul]

/-- The logarithmic derivative of the zeta Euler product is explicit. -/
theorem zeta_logDerivative (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (z : ℂ) (hz : ‖z‖ < r) :
    (∑' p : PrimePolynomial K, eulerLogDerivative 1 1 p z) =
      -(Fintype.card K : ℂ) / (1 - (Fintype.card K : ℂ) * z) := by
  have hsmall : (Fintype.card K : ℝ) * ‖z‖ < 1 :=
    (mul_le_mul_of_nonneg_left hz.le (by positivity)).trans_lt hqr
  have hlog := (hasDerivAt_logEulerSeries (1 : K[X]) monic_one 1 r hr hqr z hz).cexp
  have hlinear := ((hasDerivAt_id z).const_mul (Fintype.card K : ℂ)).const_sub 1
  have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 z :=
    Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have heq : (fun w => Complex.exp (logEulerSeries (1 : K[X]) 1 w)) =ᶠ[𝓝 z]
      (fun w => 1 - (Fintype.card K : ℂ) * w) := by
    filter_upwards [hball] with w hw
    apply exp_logEulerSeries_zeta
    have hwnorm : ‖w‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    exact (mul_le_mul_of_nonneg_left hwnorm.le (by positivity)).trans_lt hqr
  have hder := hlog.unique (hlinear.congr_of_eventuallyEq heq)
  rw [exp_logEulerSeries_zeta z hsmall] at hder
  have hne : 1 - (Fintype.card K : ℂ) * z ≠ 0 := by
    rw [← exp_logEulerSeries_zeta z hsmall]
    exact Complex.exp_ne_zero _
  apply (eq_div_iff hne).mpr
  simpa only [mul_one, mul_comm] using hder

end Erdos157.Elementary.PolynomialCharacters
