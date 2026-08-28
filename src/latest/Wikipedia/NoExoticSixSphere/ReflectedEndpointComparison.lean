import Wikipedia.NoExoticSixSphere.ReflectedEndpointFrame

/-!
# The genuine stabilized framed comparison at the initial reflected seam

The source is the actual endpoint embedding on its regular-fiber atlas,
with the canonical, normalized reflected frame. The target is the actual
initial collared zero embedding and its full outward-normal frame. The
comparison adds one axis and retains the signed normal-coordinate map.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.ReflectedSeam

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse
open ReflectedCylinder OrthogonalFrameAppend

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (hd : m = n + 6) (a : Sphere m)

def canonicalEndpointSixChange (y : Fiber d) :
    Vector ((m + 2) - 6) ≃ₗᵢ[ℝ] Vector ((m + 1 - 6) + 1) :=
  (sixColumnChange d hmiss hd y).trans
    (extendColumnChange (endpointSourceCoordinates m 6) 1).symm

def canonicalEndpointComparison (y : Fiber d) :
    let S := referenceLowCollaredState d hmiss hd a;
    letI := S.zeroAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    StabilizedFramedDiffeomorph
      (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
      (canonicalEndpointFrame d hmiss 6 hd a).normalized
      (CollaredZero.embedding S) (CollaredZero.normalFrame S y) := by
  let S := referenceLowCollaredState d hmiss hd a
  let := S.zeroAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  refine StabilizedFramedDiffeomorph.ofReverseNormal 1
    (referenceLowStateZeroDiffeomorph d hmiss hd a)
    (LinearIsometryEquiv.refl ℝ (Vector (m + 2)))
    (canonicalEndpointSixChange d hmiss hd y) ?_ ?_
  · exact referenceState_embedding d hmiss hd a
  · intro x v
    change (CollaredZero.normalFrame S y).ambient
        (referenceLowStateZeroDiffeomorph d hmiss hd a x) v =
      BlockSum.operator 1 ((canonicalEndpointFrame d hmiss 6 hd a).normalized.ambient x)
        ((extendColumnChange (endpointSourceCoordinates m 6) 1).symm
          (sixColumnChange d hmiss hd y v))
    refine (referenceState_sixFrame d hmiss hd a y x v).trans ?_
    rw [canonicalEndpointFrame_normalized_ambient]
    exact (block_comp_columnChange_symm 1
      (Orthonormalization.operator (endpointColumns d hmiss 6 hd a) x)
      (endpointSourceCoordinates m 6) (sixColumnChange d hmiss hd y v)).symm

theorem canonicalEndpointComparison_extra (y : Fiber d) :
    letI := (referenceLowCollaredState d hmiss hd a).zeroAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    (canonicalEndpointComparison d hmiss hd a y).extra = 1 := rfl

theorem canonicalEndpointComparison_diffeomorph (y : Fiber d) :
    letI := (referenceLowCollaredState d hmiss hd a).zeroAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    (canonicalEndpointComparison d hmiss hd a y).diffeomorph =
      referenceLowStateZeroDiffeomorph d hmiss hd a := rfl

end NoExoticSixSphere.ReflectedSeam
