import Wikipedia.NoExoticSixSphere.ReflectedSeamStateFrame
import Wikipedia.NoExoticSixSphere.NormalFrameCoordinateParity
import Wikipedia.NoExoticSixSphere.StabilizedFramedDiffeomorph

/-!
# The reflected endpoint frame in its native normal model

The raw reflected columns use the cylinder's normal-model dimension.
The endpoint's canonical normal model has the same dimension, but a
different expression. The dimension-only identification preserves column
order, so its Gram--Schmidt normalization agrees literally. The resulting
genuine normal frame has an actual one-axis stabilized framed comparison
with the initial collared state's full induced six-frame.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.ReflectedSeam

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse
open ReflectedCylinder OrthogonalFrameAppend

def endpointSourceCoordinates (m k : ℕ) :
    Vector (m + 1 - k) ≃ₗᵢ[ℝ] Vector ((m + 2) - (k + 1)) :=
  Orthonormalization.dimensionChange (by omega)

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (k : ℕ) (hd : m = n + k) (a : Sphere m)

def canonicalEndpointChange : Vector (m + 1 - k) ≃L[ℝ] Vector (m + 1 - k) :=
  (endpointSourceCoordinates m k).toContinuousLinearEquiv.trans
    (endpointColumnChange d hmiss k hd)

def canonicalEndpointFrame :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    SmoothRangeFrame (𝓡 k)
      (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left k hd).normalProjection
      (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left k hd).NormalModel := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  exact (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left k hd a).recoordinateModel
    (canonicalEndpointChange d hmiss k hd)

theorem canonicalEndpointFrame_ambient (x : EndpointFiber d) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (canonicalEndpointFrame d hmiss k hd a).ambient x =
      (endpointColumns d hmiss k hd a x).comp
        (endpointSourceCoordinates m k).toContinuousLinearMap := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [endpointColumns_eq_originalFrame]
  rfl

theorem canonicalEndpointFrame_normalized_ambient (x : EndpointFiber d) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (canonicalEndpointFrame d hmiss k hd a).normalized.ambient x =
      (Orthonormalization.operator (endpointColumns d hmiss k hd a) x).comp
        (endpointSourceCoordinates m k).toContinuousLinearMap := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  change Orthonormalization.operator (canonicalEndpointFrame d hmiss k hd a).ambient x = _
  have he : (canonicalEndpointFrame d hmiss k hd a).ambient =
      fun y ↦ (endpointColumns d hmiss k hd a y).comp
        (endpointSourceCoordinates m k).toContinuousLinearMap :=
    funext (canonicalEndpointFrame_ambient d hmiss k hd a)
  rw [he]
  exact Orthonormalization.operator_comp_dimensionChange
    (show m + 1 - k = (m + 2) - (k + 1) by omega)
    (endpointColumns d hmiss k hd a) x

end NoExoticSixSphere.ReflectedSeam
