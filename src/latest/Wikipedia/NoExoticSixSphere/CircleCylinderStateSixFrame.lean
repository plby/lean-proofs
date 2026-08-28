import Wikipedia.NoExoticSixSphere.CircleCylinderBoundaryColumns
import Wikipedia.NoExoticSixSphere.CircleCylinderLowCollaredState

/-!
# The actual two-ended collared state's original endpoint six-frames

Under the native endpoint-sum diffeomorphism, both full induced frames
are exactly the two-axis stabilizations of their original endpoint frames,
with fixed signed source isometries. The embeddings retain their actual
nonzero translations; a linear embedding equality is not substituted.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hd : m = n + 6) (a : Sphere 1 × Sphere m)

def sixNormalDimensionChange :
    Vector (2 + (m + 1) - 6) ≃ₗᵢ[ℝ] Vector ((2 + (m + 1) - 7) + 1) :=
  Orthonormalization.dimensionChange (by omega)

def sixColumnChange (left : Bool) :
    Vector (2 + (m + 1) - 6) ≃ₗᵢ[ℝ] Vector ((m + 1 - 6) + 2) :=
  (sixNormalDimensionChange hd).trans (boundarySourceChange 6 hd left)

theorem sixNormalDimensionChange_eq (y : Fiber d) :
    letI := fiberAtlas d 6 hd;
    letI := fiber_isManifold d 6 hd;
    sixNormalDimensionChange hd =
      EmbeddedTime.normalCoordinates (n := 6) (embedding d 6 hd) y := by
  let := fiberAtlas d 6 hd
  let := fiber_isManifold d 6 hd
  rfl

theorem sixColumnChange_apply (y : Fiber d) (left : Bool)
    (v : Vector (2 + (m + 1) - 6)) :
    letI := fiberAtlas d 6 hd;
    letI := fiber_isManifold d 6 hd;
    sixColumnChange hd left v =
      boundarySourceChange 6 hd left
        (EmbeddedTime.normalCoordinates (n := 6) (embedding d 6 hd) y v) := by
  let := fiberAtlas d 6 hd
  let := fiber_isManifold d 6 hd
  have hQ : sixNormalDimensionChange hd v =
      EmbeddedTime.normalCoordinates (n := 6) (embedding d 6 hd) y v :=
    congrArg (fun Q : Vector (2 + (m + 1) - 6) ≃ₗᵢ[ℝ]
      Vector ((2 + (m + 1) - 7) + 1) ↦ Q v) (sixNormalDimensionChange_eq d hd y)
  exact (LinearIsometryEquiv.trans_apply (sixNormalDimensionChange hd)
    (boundarySourceChange 6 hd left) v).trans
      (congrArg (boundarySourceChange 6 hd left) hQ)

theorem lowState_embedding_left (x : {x : Sphere m // d.leftMap x = b}) :
    let S := lowCollaredState d hd a;
    letI := S.zeroAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd);
    (CollaredZero.embedding S).toFun (lowStateZeroDiffeomorph d hd a (Sum.inl x)) =
      radialUnit m true + spatialIsometry m x.val.val :=
  euclideanInclusion_left d x

theorem lowState_embedding_right (x : {x : Sphere m // d.rightMap x = b}) :
    let S := lowCollaredState d hd a;
    letI := S.zeroAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd);
    (CollaredZero.embedding S).toFun (lowStateZeroDiffeomorph d hd a (Sum.inr x)) =
      radialUnit m false + spatialIsometry m x.val.val :=
  euclideanInclusion_right d x

theorem lowState_sixFrame_left (y : Fiber d) (x : {x : Sphere m // d.leftMap x = b}) :
    let S := lowCollaredState d hd a;
    letI := S.zeroAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd);
    ∀ v : Vector (2 + (m + 1) - 6),
      (CollaredZero.normalFrame S y).ambient (lowStateZeroDiffeomorph d hd a (Sum.inl x)) v =
      stabilizationAmbient m
        (BlockSum.operator 2 (Orthonormalization.operator (N := m + 1) (n := m + 1 - 6)
          (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a.2).ambient x)
            (sixColumnChange hd true v)) := by
  let S := lowCollaredState d hd a
  let := fiberAtlas d 6 hd
  let := fiber_isManifold d 6 hd
  let := S.zeroAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  change ∀ v : Vector (2 + (m + 1) - 6),
    (CollaredZero.normalFrame S y).ambient (lowStateZeroDiffeomorph d hd a (Sum.inl x)) v =
      stabilizationAmbient m
        (BlockSum.operator 2 (Orthonormalization.operator (N := m + 1) (n := m + 1 - 6)
          (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a.2).ambient x)
            (sixColumnChange hd true v))
  intro v
  let E : Vector (m + 1 - 6) →L[ℝ] Vector (m + 1) :=
    Orthonormalization.operator (N := m + 1) (n := m + 1 - 6)
      (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a.2).ambient x
  have h : EmbeddedTime.zeroColumns (n := 6) (embedding d 6 hd) (CollaredZero.retraction S y)
      (timeMap d) (euclideanNormalFrame d a 6 hd)
        ⟨leftInclusion d x, time_leftInclusion d x⟩ =
      ((stabilizationAmbient m).toContinuousLinearMap.comp (BlockSum.operator 2 E)).comp
        (boundarySourceChange 6 hd true).toContinuousLinearMap :=
    zeroColumns_left d a 6 hd x (CollaredZero.retraction S y)
  refine (congrArg (fun L : Vector ((2 + (m + 1) - 7) + 1) →L[ℝ] Vector (2 + (m + 1)) ↦
    L (EmbeddedTime.normalCoordinates (n := 6) (embedding d 6 hd) y v)) h).trans ?_
  have hQ := sixColumnChange_apply d hd y true v
  have hs := Eq.symm hQ
  change stabilizationAmbient m (BlockSum.operator 2 E
      (boundarySourceChange 6 hd true
        (EmbeddedTime.normalCoordinates (n := 6) (embedding d 6 hd) y v))) =
    stabilizationAmbient m (BlockSum.operator 2 E (sixColumnChange hd true v))
  rw [hs]

theorem lowState_sixFrame_right (y : Fiber d) (x : {x : Sphere m // d.rightMap x = b}) :
    let S := lowCollaredState d hd a;
    letI := S.zeroAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd);
    ∀ v : Vector (2 + (m + 1) - 6),
      (CollaredZero.normalFrame S y).ambient (lowStateZeroDiffeomorph d hd a (Sum.inr x)) v =
      stabilizationAmbient m
        (BlockSum.operator 2 (Orthonormalization.operator (N := m + 1) (n := m + 1 - 6)
          (RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right 6 hd a.2).ambient x)
            (sixColumnChange hd false v)) := by
  let S := lowCollaredState d hd a
  let := fiberAtlas d 6 hd
  let := fiber_isManifold d 6 hd
  let := S.zeroAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  change ∀ v : Vector (2 + (m + 1) - 6),
    (CollaredZero.normalFrame S y).ambient (lowStateZeroDiffeomorph d hd a (Sum.inr x)) v =
      stabilizationAmbient m
        (BlockSum.operator 2 (Orthonormalization.operator (N := m + 1) (n := m + 1 - 6)
          (RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right 6 hd a.2).ambient x)
            (sixColumnChange hd false v))
  intro v
  let E : Vector (m + 1 - 6) →L[ℝ] Vector (m + 1) :=
    Orthonormalization.operator (N := m + 1) (n := m + 1 - 6)
      (RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right 6 hd a.2).ambient x
  have h : EmbeddedTime.zeroColumns (n := 6) (embedding d 6 hd) (CollaredZero.retraction S y)
      (timeMap d) (euclideanNormalFrame d a 6 hd)
        ⟨rightInclusion d x, time_rightInclusion d x⟩ =
      ((stabilizationAmbient m).toContinuousLinearMap.comp (BlockSum.operator 2 E)).comp
        (boundarySourceChange 6 hd false).toContinuousLinearMap :=
    zeroColumns_right d a 6 hd x (CollaredZero.retraction S y)
  refine (congrArg (fun L : Vector ((2 + (m + 1) - 7) + 1) →L[ℝ] Vector (2 + (m + 1)) ↦
    L (EmbeddedTime.normalCoordinates (n := 6) (embedding d 6 hd) y v)) h).trans ?_
  have hQ := sixColumnChange_apply d hd y false v
  have hs := Eq.symm hQ
  change stabilizationAmbient m (BlockSum.operator 2 E
      (boundarySourceChange 6 hd false
        (EmbeddedTime.normalCoordinates (n := 6) (embedding d 6 hd) y v))) =
    stabilizationAmbient m (BlockSum.operator 2 E (sixColumnChange hd false v))
  rw [hs]

end NoExoticSixSphere.CircleCylinder
