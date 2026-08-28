import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! # Vanishing orders under genuine analytic coordinate changes

An actual complex local biholomorphism has nonzero derivative, so subtracting
its value at the basepoint gives a simple zero.  The analytic composition
formula then proves that changing the target coordinate preserves centered
vanishing orders, including the order of an identically vanishing germ.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.SourceOrders

/-- The differential equivalence of an actual complex local biholomorphism
forces its scalar derivative to be nonzero. -/
theorem deriv_ne_zero_of_isLocalDiffeomorph {f : ℂ → ℂ} {z : ℂ}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) : deriv f z ≠ 0 := by
  let e : ℂ ≃L[ℂ] ℂ := hf.mfderivToContinuousLinearEquiv (by simp)
  have he : e 1 = deriv f z := by
    change (show ℂ →L[ℂ] ℂ from mfderiv 𝓘(ℂ) 𝓘(ℂ) f z) 1 = deriv f z
    rw [mfderiv_eq_fderiv]
    rfl
  intro h
  have h10 : e 1 = e 0 := by rw [he, h, map_zero]
  exact one_ne_zero (e.injective h10)

/-- Subtracting the value of a local biholomorphism gives a simple zero;
the value of the original function need not be zero. -/
theorem centered_order_eq_one_of_isLocalDiffeomorph {f : ℂ → ℂ} {z : ℂ}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) :
    analyticOrderAt (fun w => f w - f z) z = 1 :=
  hf.contMDiffAt.contDiffAt.analyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero
    (deriv_ne_zero_of_isLocalDiffeomorph hf)

/-- A zero of an actual local biholomorphism is simple. -/
theorem order_eq_one_of_isLocalDiffeomorph {f : ℂ → ℂ} {z : ℂ}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) (hz : f z = 0) :
    analyticOrderAt f z = 1 := by
  simpa only [hz, sub_zero] using centered_order_eq_one_of_isLocalDiffeomorph hf

/-- A genuine local biholomorphic change of target coordinate preserves
the centered vanishing order of an analytic germ.  No zero-value or
nonconstant-germ hypothesis is required. -/
theorem centered_order_comp {F f : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a)
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f (F a)) :
    analyticOrderAt (fun w => f (F w) - f (F a)) a =
      analyticOrderAt (fun w => F w - F a) a := by
  have houter : AnalyticAt ℂ (fun w => f w - f (F a)) (F a) :=
    hf.contMDiffAt.contDiffAt.analyticAt.sub analyticAt_const
  simpa only [Function.comp_def, centered_order_eq_one_of_isLocalDiffeomorph hf,
    one_mul] using houter.analyticOrderAt_comp hF

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.SourceOrders
