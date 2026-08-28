import Wikipedia.NoExoticSixSphere.ReflectedFillingFrame
import Wikipedia.NoExoticSixSphere.ReflectedEndpointArf

/-!
# The canonical original endpoint frame reaches the literal filling boundary

Compose the actual initial one-axis framed comparison with the full
connectivity-surgery and filling-boundary comparison. The result starts
from the original endpoint embedding and its genuine canonical normal
frame, whose Arf invariant has been identified with the original one.
Its diffeomorphism is exactly the constructed filling's boundary map.
The source frame is not replaced by an assumed comparison.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.ReflectedSeam

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse ReflectedCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (hd : m = n + 6) (a : Sphere m)
  (x₀ : EndpointFiber d) {U : CollaredSevenState (EndpointFiber d)}
  (F : CollaredFillingBoundary.Comparison (referenceLowCollaredState d hmiss hd a) U x₀)

def canonicalEndpointFillingComparison :
    letI := U.halfBoundaryAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    StabilizedFramedDiffeomorph
      (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
      (canonicalEndpointFrame d hmiss 6 hd a).normalized
      (CollaredFillingBoundary.embedding U)
      (CollaredFillingBoundary.normalFrame U (U.collar.zeroPoint x₀).val) := by
  let S := referenceLowCollaredState d hmiss hd a
  let := S.zeroAtlas
  let := U.halfBoundaryAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  exact (canonicalEndpointComparison d hmiss hd a (CollaredZero.referencePoint S x₀)).trans F

theorem canonicalEndpointFillingComparison_extra :
    letI := (referenceLowCollaredState d hmiss hd a).zeroAtlas;
    letI := U.halfBoundaryAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    (canonicalEndpointFillingComparison d hmiss hd a x₀ F).extra = 1 + F.extra := rfl

theorem canonicalEndpointFillingComparison_diffeomorph :
    letI := (referenceLowCollaredState d hmiss hd a).zeroAtlas;
    letI := U.halfBoundaryAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    (canonicalEndpointFillingComparison d hmiss hd a x₀ F).diffeomorph =
      (referenceLowStateZeroDiffeomorph d hmiss hd a).trans F.diffeomorph := rfl

theorem canonicalEndpointFillingComparison_boundary (x : EndpointFiber d) :
    letI := U.halfBoundaryAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    ((canonicalEndpointFillingComparison d hmiss hd a x₀ F).diffeomorph x).val =
      ((endpointFilling d hmiss hd a x₀ F).boundaryDiffeomorph x).val := rfl

end NoExoticSixSphere.ReflectedSeam
