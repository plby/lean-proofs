import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Second derivative comparison at a touching point

If two twice differentiable functions agree at a point and the first is no
greater than the second nearby, their second derivatives have the same order.
This transfers a negative energy direction to an energy-minimizing replacement.
-/

open Filter
open scoped Topology

namespace NoExoticSixSphere.SecondDerivativeComparison

theorem nonneg_of_localMin {f : ℝ → ℝ} {s : ℝ}
    (hmin : IsLocalMin f s) (hc : ContinuousAt f s) : 0 ≤ deriv (deriv f) s := by
  by_contra h
  have hneg : deriv (deriv f) s < 0 := lt_of_not_ge h
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 s] (fun _ ↦ f s) := by
    filter_upwards [hmin, hmax] with t ht ht'
    exact le_antisymm ht' ht
  have hz : deriv (deriv f) s = 0 := by
    have hconst : deriv (fun _ : ℝ ↦ f s) = (fun _ : ℝ ↦ (0 : ℝ)) := by
      funext t
      exact deriv_const t (f s)
    simpa only [hconst, deriv_const] using heq.deriv.deriv_eq
  linarith

theorem le_of_touching {f g : ℝ → ℝ} {s f'' g'' : ℝ}
    (hf : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ f t)
    (hg : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t)
    (hfc : ContinuousAt f s) (hgc : ContinuousAt g s)
    (hf'' : HasDerivAt (deriv f) f'' s) (hg'' : HasDerivAt (deriv g) g'' s)
    (heq : f s = g s) (hle : ∀ᶠ t in 𝓝 s, f t ≤ g t) : f'' ≤ g'' := by
  have hmin : IsLocalMin (fun t ↦ g t - f t) s := by
    filter_upwards [hle] with t ht
    change g s - f s ≤ g t - f t
    rw [heq, sub_self]
    exact sub_nonneg.mpr ht
  have hderiv : deriv (fun t ↦ g t - f t) =ᶠ[𝓝 s] (fun t ↦ deriv g t - deriv f t) := by
    filter_upwards [hf, hg] with t hft hgt
    exact deriv_sub hgt hft
  have hd : HasDerivAt (deriv (fun t ↦ g t - f t)) (g'' - f'') s :=
    (hg''.sub hf'').congr_of_eventuallyEq hderiv
  have hnonneg := nonneg_of_localMin hmin (hgc.sub hfc)
  rw [hd.deriv] at hnonneg
  linarith

end NoExoticSixSphere.SecondDerivativeComparison
