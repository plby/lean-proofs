import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenRecognition
import Wikipedia.HopfProblem.DegreeCollapseReflectedTimeCollar
import Wikipedia.HopfProblem.DegreeCollapseReflectedTimeZeroDiffeomorph

/-!

# The original regular cylinder supplies a native state before low surgery

The reflected fiber, native atlas, closed embedding, full normal framing,
regular time and actual seam collar supply the unrestricted low-surgery
state. No homology or connectivity hypothesis is required for these data.
The original endpoint regular-fiber atlas is retained by the literal seam
diffeomorphism to the state's independently constructed native zero fiber.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (hdim : m = n + 6) (a : Sphere m)

def referenceLowCollaredState : LowCollaredSevenState (EndpointFiber d) := by
  let := fiberAtlas d 6 hdim
  let := fiber_isManifold d 6 hdim
  let := compactSpace_fiber d hmiss
  exact LowCollaredSevenState.ofCollar (embedding d hmiss 6 hdim)
    (euclideanNormalFraming d hmiss 6 hdim a) (time d) (contMDiff_time d 6 hdim)
    (regular_time_zero d 6 hdim) (seamTimeCollar d)

def referenceLowStateZeroDiffeomorph :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim)
    letI := (referenceLowCollaredState d hmiss hdim a).zeroAtlas
    EndpointFiber d ≃ₘ⟮𝓡 6, 𝓡 6⟯ (referenceLowCollaredState d hmiss hdim a).Zero := by
  let := fiberAtlas d 6 hdim
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim)
  let := timeZeroAtlas d 6 hdim
  exact timeZeroDiffeomorph d 6 hdim

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
