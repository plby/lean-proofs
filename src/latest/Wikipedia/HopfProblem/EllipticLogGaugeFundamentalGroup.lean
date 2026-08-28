import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupGauge
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupFibres

/-!
# Actual logarithmic elliptic attaching paths and their fundamental-group markings

The logarithmic inverse-gauge meridian has a real lift ending at the affine
generator, hence has inverse-generator marking under the native monodromy
convention.  Positive straight period loops have negative translation
marking under the same convention.  Every positive radius admits an actual
normalized logarithm putting these loops inside the corresponding tube.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

/-- The required logarithmic basepoint can always be chosen, at any prescribed
positive radius.  Its existence is not an attaching-map assumption. -/
theorem exists_logMeridian_parameters (j : Kind) (r : ℝ) (hr : 0 < r) :
    ∃ s : ℂ, 0 < s.im ∧ ‖exponential s‖ ^ j.order < r := by
  let a : ℝ := min r 1 / 2
  have ha0 : 0 < a := half_pos (lt_min hr zero_lt_one)
  have ha1 : a < 1 := by
    have h := min_le_right r (1 : ℝ)
    dsimp only [a]
    linarith
  have har : a < r := by
    have h := min_le_left r (1 : ℝ)
    dsimp only [a] at ha0 ⊢
    linarith
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hnorm : ‖exponential (logarithm (a : ℂ))‖ = a := by
    rw [exponential_logarithm hane, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
  have hpow : a ^ j.order ≤ a := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero j.order_pos.ne'
    rw [hn, pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ha0.le ha1.le) ha0.le).trans_eq
      (one_mul a)
  refine ⟨logarithm (a : ℂ), ?_, ?_⟩
  · exact TauCusp.upperHalfPlane_of_exponential_norm_lt_one (by rw [hnorm]; exact ha1)
  · rw [hnorm]
    exact hpow.trans_lt har

end Wikipedia.HopfProblem.Elliptic.LogGauge
