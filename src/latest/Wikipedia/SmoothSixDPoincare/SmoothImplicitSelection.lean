import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Smoothness of an existing continuous implicit solution

The implicit-function theorem is used to identify an already given
continuous solution, including on a restricted parameter set. Thus an
original hitting-time function can acquire smoothness without replacing it
by a different choice of root.
-/

noncomputable section

open Filter Set Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem contDiffWithinAt_implicitSelection {f : E × F → G} {g : E → F}
    {s : Set E} {x : E} (hf : ContDiffAt ℝ ∞ f (x, g x))
    (hinv : (fderiv ℝ f (x, g x) ∘L ContinuousLinearMap.inr ℝ E F).IsInvertible)
    (hg : ContinuousWithinAt g s x)
    (heq : ∀ᶠ y in 𝓝[s] x, f (y, g y) = f (x, g x)) :
    ContDiffWithinAt ℝ ∞ g s x := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let ψ := hf.implicitFunction hn hinv
  have hψ : ContDiffAt ℝ ∞ ψ x := hf.contDiffAt_implicitFunction hn hinv
  have hpair : Tendsto (fun y => (y, g y)) (𝓝[s] x) (𝓝 (x, g x)) :=
    continuousWithinAt_id.prodMk hg
  have hloc := hpair.eventually (hf.eventually_apply_eq_iff_implicitFunction hn hinv)
  have hsame : g =ᶠ[𝓝[s] x] ψ := by
    filter_upwards [hloc, heq] with y hy hy'
    exact (hy.mp hy').symm
  exact hψ.contDiffWithinAt.congr_of_eventuallyEq hsame
    (hf.implicitFunction_apply_self hn hinv).symm

omit [CompleteSpace E] in
theorem scalar_partial_invertible {f : E × ℝ → ℝ} {x : E} {t d : ℝ}
    (hf : ContDiffAt ℝ ∞ f (x, t)) (hd : HasDerivAt (fun s => f (x, s)) d t)
    (hd₀ : d ≠ 0) :
    (fderiv ℝ f (x, t) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
  have hpair : HasFDerivAt (fun s : ℝ => (x, s)) (ContinuousLinearMap.inr ℝ E ℝ) t :=
    (hasFDerivAt_const x t).prodMk (hasFDerivAt_id t)
  have h := (hf.differentiableAt (by simp)).hasFDerivAt.comp t hpair
  have heq := h.unique (hd.hasFDerivAt_equiv hd₀)
  rw [heq]
  exact ContinuousLinearMap.isInvertible_equiv

theorem contDiffWithinAt_scalarImplicitSelection {f : E × ℝ → ℝ} {g : E → ℝ}
    {s : Set E} {x : E} {d : ℝ} (hf : ContDiffAt ℝ ∞ f (x, g x))
    (hd : HasDerivAt (fun t => f (x, t)) d (g x)) (hd₀ : d ≠ 0)
    (hg : ContinuousWithinAt g s x)
    (heq : ∀ᶠ y in 𝓝[s] x, f (y, g y) = f (x, g x)) :
    ContDiffWithinAt ℝ ∞ g s x :=
  contDiffWithinAt_implicitSelection hf (scalar_partial_invertible hf hd hd₀) hg heq

end Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus
