import ErdosProblems.Erdos421.ZetaErrorIdentity
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # Removing the pole before comparing von Mangoldt sums with integer sums -/

namespace Erdos421

open Complex Filter Topology

theorem riemannZeta₁_eq_sub_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

theorem riemannZeta₁_ne_zero_of_zeta_ne_zero {s : ℂ} (hs : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) : riemannZeta₁ s ≠ 0 := by
  rw [riemannZeta₁_eq_sub_mul hs]
  exact mul_ne_zero (sub_ne_zero.mpr hs) hζ

theorem riemannZeta₁_ne_zero_on_right {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  by_cases h : s = 1
  · simp only [h, riemannZeta₁_one, ne_eq, one_ne_zero, not_false_eq_true]
  exact riemannZeta₁_ne_zero_of_zeta_ne_zero h (riemannZeta_ne_zero_of_one_le_re hs)

theorem logDeriv_riemannZeta₁_eq {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannZeta₁ s = logDeriv riemannZeta s + (s - 1)⁻¹ := by
  have hz : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hζ₁ : riemannZeta₁ s ≠ 0 := riemannZeta₁_ne_zero_of_zeta_ne_zero hs hζ
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs,
    riemannZeta_eq_inv_sub_mul hs]
  field_simp
  ring

theorem analyticAt_logDeriv_riemannZeta₁ {s : ℂ} (hs : riemannZeta₁ s ≠ 0) :
    AnalyticAt ℂ (logDeriv riemannZeta₁) s := by
  have h := differentiable_riemannZeta₁.analyticAt (z := s)
  exact h.deriv.div h hs

noncomputable def zetaPrimeError (s : ℂ) : ℂ := logDeriv riemannZeta₁ s + riemannZeta₀ s

theorem zetaPrimeError_eq {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    zetaPrimeError s = logDeriv riemannZeta s + riemannZeta s := by
  rw [zetaPrimeError, logDeriv_riemannZeta₁_eq hs hζ, riemannZeta_eq_inv_sub_add hs]
  ring

theorem analyticAt_zetaPrimeError {s : ℂ} (hs : riemannZeta₁ s ≠ 0) :
    AnalyticAt ℂ zetaPrimeError s :=
  (analyticAt_logDeriv_riemannZeta₁ hs).add (differentiable_riemannZeta₀.analyticAt (z := s))

end Erdos421
