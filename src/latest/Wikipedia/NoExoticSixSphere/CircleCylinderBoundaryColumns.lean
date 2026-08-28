import Wikipedia.NoExoticSixSphere.CircleCylinderOriginalEndpointColumns
import Wikipedia.NoExoticSixSphere.CircleCylinderTwoAxisCoordinates
import Wikipedia.NoExoticSixSphere.CircleCylinderSeamGradient

/-!
# Both complete induced boundary frames are signed two-axis stabilizations

These identities concern the full normal operators, not merely their
ranges. They retain the original endpoint frames and atlases, the actual
dimension changes, the leading radial column, and the negative time normal.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization Stiefel

def boundarySourceChange {m n : ℕ} (k : ℕ) (hd : m = n + k) (left : Bool) :
    Vector ((2 + (m + 1) - (k + 1)) + 1) ≃ₗᵢ[ℝ] Vector ((m + 1 - k) + 2) :=
  (OrthogonalFrameAppend.extendColumnChange (normalDimensionChange k hd) 1).trans
    ((boundaryColumnIsometry (n + 1) left).trans
      (OrthogonalFrameAppend.extendColumnChange (endpointColumnChange k hd) 2))

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem zeroColumns_left (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.leftMap x = b}) :
    letI := fiberAtlas d k hd;
    letI := fiber_isManifold d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    ∀ r : (embedding d k hd).TubularRetraction,
      EmbeddedTime.zeroColumns (n := k) (embedding d k hd) r (timeMap d)
        (euclideanNormalFrame d a k hd) ⟨leftInclusion d x, time_leftInclusion d x⟩ =
      ((stabilizationAmbient m).toContinuousLinearMap.comp
        (BlockSum.operator 2 (Orthonormalization.operator
          (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left k hd a.2
            ).ambient x))).comp (boundarySourceChange k hd true).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  intro r
  let B : Vector (2 + (m + 1) - (k + 1)) →L[ℝ] Vector (2 + (m + 1)) :=
    Orthonormalization.operator (euclideanNormalFrame d a k hd).ambient (leftInclusion d x)
  let E : Vector (m + 1 - k) →L[ℝ] Vector (m + 1) :=
    Orthonormalization.operator
      (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left k hd a.2).ambient x
  have hB : B = (OrthogonalFramePrepend.operator (radialUnit m true)
      ((spatialIsometry m).toContinuousLinearMap.comp
        (Orthonormalization.operator (leftEndpointColumns d a.2 k hd) x))).comp
          (normalDimensionChange k hd).toContinuousLinearMap :=
    normalized_euclideanNormalFrame_left d a k hd x
  have hE : Orthonormalization.operator (leftEndpointColumns d a.2 k hd) x =
      E.comp (endpointColumnChange k hd).toContinuousLinearMap :=
    normalized_leftEndpointColumns d a.2 k hd x
  calc
    _ = OrthogonalFrameAppend.operator B (-timeUnit m) :=
      congrArg (OrthogonalFrameAppend.operator B)
        (outwardNormal_seam d a k hd ⟨leftInclusion d x, time_leftInclusion d x⟩ r)
    _ = ((stabilizationAmbient m).toContinuousLinearMap.comp (BlockSum.operator 2 E)).comp
        (boundarySourceChange k hd true).toContinuousLinearMap := by
      rw [hB, OrthogonalFrameAppend.operator_comp_columnChange, append_prepend_eq_twoAxisBlock,
        hE, OrthogonalFrameAppend.block_comp_columnChange]
      apply ContinuousLinearMap.ext
      intro v
      simp only [boundarySourceChange, ContinuousLinearMap.comp_apply,
        LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.trans_apply]

theorem zeroColumns_right (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.rightMap x = b}) :
    letI := fiberAtlas d k hd;
    letI := fiber_isManifold d k hd;
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    ∀ r : (embedding d k hd).TubularRetraction,
      EmbeddedTime.zeroColumns (n := k) (embedding d k hd) r (timeMap d)
        (euclideanNormalFrame d a k hd) ⟨rightInclusion d x, time_rightInclusion d x⟩ =
      ((stabilizationAmbient m).toContinuousLinearMap.comp
        (BlockSum.operator 2 (Orthonormalization.operator
          (RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right k hd a.2
            ).ambient x))).comp (boundarySourceChange k hd false).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  intro r
  let B : Vector (2 + (m + 1) - (k + 1)) →L[ℝ] Vector (2 + (m + 1)) :=
    Orthonormalization.operator (euclideanNormalFrame d a k hd).ambient (rightInclusion d x)
  let E : Vector (m + 1 - k) →L[ℝ] Vector (m + 1) :=
    Orthonormalization.operator
      (RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right k hd a.2).ambient x
  have hB : B = (OrthogonalFramePrepend.operator (radialUnit m false)
      ((spatialIsometry m).toContinuousLinearMap.comp
        (Orthonormalization.operator (rightEndpointColumns d a.2 k hd) x))).comp
          (normalDimensionChange k hd).toContinuousLinearMap :=
    normalized_euclideanNormalFrame_right d a k hd x
  have hE : Orthonormalization.operator (rightEndpointColumns d a.2 k hd) x =
      E.comp (endpointColumnChange k hd).toContinuousLinearMap :=
    normalized_rightEndpointColumns d a.2 k hd x
  calc
    _ = OrthogonalFrameAppend.operator B (-timeUnit m) :=
      congrArg (OrthogonalFrameAppend.operator B)
        (outwardNormal_seam d a k hd ⟨rightInclusion d x, time_rightInclusion d x⟩ r)
    _ = ((stabilizationAmbient m).toContinuousLinearMap.comp (BlockSum.operator 2 E)).comp
        (boundarySourceChange k hd false).toContinuousLinearMap := by
      rw [hB, OrthogonalFrameAppend.operator_comp_columnChange, append_prepend_eq_twoAxisBlock,
        hE, OrthogonalFrameAppend.block_comp_columnChange]
      apply ContinuousLinearMap.ext
      intro v
      simp only [boundarySourceChange, ContinuousLinearMap.comp_apply,
        LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.trans_apply]

end NoExoticSixSphere.CircleCylinder
