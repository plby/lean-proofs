import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic

/-!
# Detecting equality of local analytic fractions

Nonzero analytic denominator germs are nonzero off the center on a
sufficiently small punctured neighborhood.  Equality of their scalar
fractions there forces the holomorphic cross product to have zero germ.
Values assigned at a pole play no role.
-/

noncomputable section

open Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereRepresentative

/-- Punctured agreement of genuine analytic fractions gives equality of
their holomorphic cross products as ordinary neighborhood germs. -/
theorem analytic_cross_eventuallyEq_zero_of_fraction_eventuallyEq
    {p q r s : ℂ → ℂ} {z : ℂ}
    (hp : AnalyticAt ℂ p z) (hq : AnalyticAt ℂ q z)
    (hr : AnalyticAt ℂ r z) (hs : AnalyticAt ℂ s z)
    (hqne : ¬ q =ᶠ[𝓝 z] 0) (hsne : ¬ s =ᶠ[𝓝 z] 0)
    (he : (fun w => p w / q w) =ᶠ[𝓝[≠] z] (fun w => r w / s w)) :
    (fun w => p w * s w - r w * q w) =ᶠ[𝓝 z] 0 := by
  have hq' : ∀ᶠ w in 𝓝[≠] z, q w ≠ 0 :=
    hq.eventually_eq_zero_or_eventually_ne_zero.resolve_left hqne
  have hs' : ∀ᶠ w in 𝓝[≠] z, s w ≠ 0 :=
    hs.eventually_eq_zero_or_eventually_ne_zero.resolve_left hsne
  have hcross : ∀ᶠ w in 𝓝[≠] z, p w * s w - r w * q w = 0 := by
    filter_upwards [he, hq', hs'] with w hw hqw hsw
    exact sub_eq_zero.mpr ((div_eq_div_iff hqw hsw).mp hw)
  exact ((hp.mul hs).sub (hr.mul hq)).frequently_zero_iff_eventually_zero.mp
    hcross.frequently

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereRepresentative
