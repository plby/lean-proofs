import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth scalar hitting-time germs from a transverse crossing

The time derivative is the actual one-dimensional derivative of the
supplied smooth family. Its nonvanishing constructs the invertibility
required by the implicit-function theorem and gives a genuine smooth
root germ with the original level value.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [CompleteSpace P] in
theorem scalar_partial_invertible {F : P × ℝ → ℝ} {p : P} {t v : ℝ}
    (hF : ContDiffAt ℝ ∞ F (p, t))
    (htime : HasDerivAt (fun s : ℝ => F (p, s)) v t) (hv : v ≠ 0) :
    ((fderiv ℝ F (p, t)).comp (ContinuousLinearMap.inr ℝ P ℝ)).IsInvertible := by
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp t
    ((hasFDerivAt_const p t).prodMk (hasFDerivAt_id t))
  change HasFDerivAt (fun s : ℝ => F (p, s))
    ((fderiv ℝ F (p, t)).comp (ContinuousLinearMap.inr ℝ P ℝ)) t at hd
  have heq := hd.unique htime.hasFDerivAt
  let L : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ v hv).toContinuousLinearEquiv
  refine ⟨L, ?_⟩
  rw [heq]
  apply ContinuousLinearMap.ext
  intro r
  change v * r = r * v
  exact mul_comm v r

/-- A transverse time derivative constructs an actual smooth local hitting time. -/
theorem exists_smooth_scalar_time_germ {F : P × ℝ → ℝ} {p : P} {t c v : ℝ}
    (hF : ContDiffAt ℝ ∞ F (p, t)) (hlevel : F (p, t) = c)
    (htime : HasDerivAt (fun s : ℝ => F (p, s)) v t) (hv : v ≠ 0) :
    ∃ θ : P → ℝ, θ p = t ∧ ContDiffAt ℝ ∞ θ p ∧
      ∀ᶠ q in 𝓝 p, F (q, θ q) = c := by
  have hinv := scalar_partial_invertible hF htime hv
  let θ := hF.implicitFunction (by simp) hinv
  refine ⟨θ, hF.implicitFunction_apply_self (by simp) hinv,
    hF.contDiffAt_implicitFunction (by simp) hinv, ?_⟩
  filter_upwards [hF.eventually_apply_implicitFunction (by simp) hinv] with q hq
  exact hq.trans hlevel

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
