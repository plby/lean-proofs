import Wikipedia.HopfProblem.DegreeCollapseReflectedLowCollaredState
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenFillingRecognition

/-!

# The actual cylinder endpoint is standard from the framed filling alone

The reflected native cylinder supplies the actual framed collared state.
Component restriction and low surgery construct the required connectivity
properties. Compose the retained native zero-atlas diffeomorphism with
the resulting sphere recognition. No half-connectivity or homology input
is used; the initial cylinder remains a genuine supplied input.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere

theorem nonempty_endpoint_sphere_diffeomorph_of_framed_filling {m n : ℕ} {b : Sphere n}
    (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
    (hmiss : ∀ x, d.rightMap x ≠ b) (hdim : m = n + 6) (a : Sphere m)
    (eBoundary : EndpointFiber d ≃ₜ Sphere 6) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim)
    Nonempty (EndpointFiber d ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim)
  let S := referenceLowCollaredState d hmiss hdim a
  let := S.zeroAtlas
  obtain ⟨D⟩ := S.nonempty_zero_sphere_diffeomorph_of_filling eBoundary
  exact ⟨(referenceLowStateZeroDiffeomorph d hmiss hdim a).trans D⟩

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
