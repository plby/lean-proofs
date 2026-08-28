import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerCoefficients

/-!
# Removing the initial monomial from an analytic cyclic germ

Vanishing of the initial Taylor coefficients gives an actual analytic quotient
by a power of the coordinate, using iterated divided differences.  A weighted
cyclic covariance then becomes ordinary invariance of that quotient.
-/

noncomputable section

open Filter Function
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

/-- An analytic germ whose first `r` coefficients vanish has an analytic factor
after division by `s ^ r`.  The divided-difference construction gives the
displayed equality for every `s`, not merely on a punctured neighborhood. -/
theorem analyticAt_pow_factor_of_coeff_zero
    {F : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt F p 0) {r : ℕ}
    (hzero : ∀ n < r, p n (fun _ => 1) = 0) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ ∀ s, F s = s ^ r * A s := by
  have hzero' : ∀ n < r, (Function.swap dslope 0)^[n] F 0 = 0 := by
    intro n hn
    rw [← (hp.has_fpower_series_iterate_dslope_fslope n).coeff_zero 1,
      ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope,
      zero_add, FormalMultilinearSeries.coeff]
    exact hzero n hn
  refine ⟨(Function.swap dslope 0)^[r] F,
    ⟨_, hp.has_fpower_series_iterate_dslope_fslope r⟩, ?_⟩
  intro s
  simpa only [sub_zero, smul_eq_mul] using
    (pow_sub_smul_iterate_dslope_of_zero r hzero' s).symm

/-- Root covariance forces the initial monomial of an analytic germ.  This
version needs no prior coefficient-vanishing or descent assumption. -/
theorem analyticAt_pow_factor_of_covariance
    {F : ℂ → ℂ} {ζ : ℂ} {m k : ℕ}
    (hζ : IsPrimitiveRoot ζ m) (hF : AnalyticAt ℂ F 0)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (ζ * s) * ζ ^ k = F s)
    (hk : 0 < k) (hkm : k ≤ m) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ ∀ s, F s = s ^ (m - k) * A s := by
  obtain ⟨p, hp⟩ := hF
  exact analyticAt_pow_factor_of_coeff_zero hp fun n hn =>
    powerSeries_coefficient_eq_zero_of_lt_sub hζ hp hcov hk hkm hn

/-- After factoring the initial monomial, a cyclic weight is cancelled by that
monomial whenever the combined exponent is a period of the root of unity. -/
theorem eventually_invariant_of_pow_factor
    {F A : ℂ → ℂ} {ζ : ℂ} {r k : ℕ}
    (hfactor : ∀ s, F s = s ^ r * A s)
    (hperiod : ζ ^ (r + k) = 1)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (ζ * s) * ζ ^ k = F s) :
    ∀ᶠ s in 𝓝 (0 : ℂ), A (ζ * s) = A s := by
  filter_upwards [hcov] with s hs
  by_cases hs0 : s = 0
  · simp [hs0]
  have hleft : (ζ * s) ^ r * A (ζ * s) * ζ ^ k =
      s ^ r * A (ζ * s) := by
    calc
      _ = s ^ r * A (ζ * s) * (ζ ^ r * ζ ^ k) := by rw [mul_pow]; ring
      _ = s ^ r * A (ζ * s) := by rw [← pow_add, hperiod, mul_one]
  rw [hfactor (ζ * s), hfactor s, hleft] at hs
  exact (mul_left_cancel₀ (pow_ne_zero r hs0)) hs

/-- The invariant analytic factor is constructed from the original analytic
function and its coefficients; it is not an extra descent hypothesis. -/
theorem analyticAt_invariant_pow_factor_of_coeff_zero
    {F : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt F p 0) {ζ : ℂ} {r k : ℕ}
    (hzero : ∀ n < r, p n (fun _ => 1) = 0)
    (hperiod : ζ ^ (r + k) = 1)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (ζ * s) * ζ ^ k = F s) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ (∀ s, F s = s ^ r * A s) ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), A (ζ * s) = A s := by
  obtain ⟨A, hA, hfactor⟩ := analyticAt_pow_factor_of_coeff_zero hp hzero
  exact ⟨A, hA, hfactor, eventually_invariant_of_pow_factor hfactor hperiod hcov⟩

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
