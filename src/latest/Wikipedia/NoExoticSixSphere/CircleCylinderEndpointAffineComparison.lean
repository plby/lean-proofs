import Wikipedia.NoExoticSixSphere.CircleCylinderClopenEndpointFrames
import Wikipedia.NoExoticSixSphere.AffineStabilizedFramedDiffeomorph
import Wikipedia.NoExoticSixSphere.OrthonormalRangeFrame

/-!
# Genuine affine framed comparisons with both original endpoints

The source is each original regular-fiber embedding and its normalized
original frame. The target is its actual native clopen seam embedding and
the restricted induced frame. Two axes are added; the signed radial
translation, ambient isometry, and full signed source isometry are retained.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization Stiefel

theorem stabilizationAmbient_appendZero (m : ℕ) (v : Vector (m + 1)) :
    stabilizationAmbient m (appendZeroMap (m + 1) 2 v) = spatialIsometry m v :=
  stabilizationAmbient_apply m v 0

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hd : m = n + 6) (a : Sphere 1 × Sphere m)

def leftEndpointAffineComparison (y : Fiber d) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := timeZeroAtlas d 6 hd;
    AffineStabilizedFramedDiffeomorph
      (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
      (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a.2).normalized
      (leftZeroEmbedding d hd a) (leftZeroFrame d hd a y) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  refine AffineStabilizedFramedDiffeomorph.ofReverseNormal 2 (leftZeroDiffeomorph d 6 hd)
    (stabilizationAmbient m) (radialUnit m true) (sixColumnChange hd true) ?_ ?_
  · intro x
    calc
      _ = radialUnit m true + spatialIsometry m x.val.val := leftZeroEmbedding_apply d hd a x
      _ = radialUnit m true + stabilizationAmbient m (appendZeroMap (m + 1) 2 x.val.val) :=
        congrArg (fun w : Vector (2 + (m + 1)) ↦ radialUnit m true + w)
          (stabilizationAmbient_appendZero m x.val.val).symm
  · intro x v
    exact leftZeroFrame_apply d hd a y x v

def rightEndpointAffineComparison (y : Fiber d) :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd);
    letI := timeZeroAtlas d 6 hd;
    AffineStabilizedFramedDiffeomorph
      (RegularSphereFiber.embedding d.rightMap d.smooth_right b d.regular_right 6 hd)
      (RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right 6 hd a.2).normalized
      (rightZeroEmbedding d hd a) (rightZeroFrame d hd a y) := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  refine AffineStabilizedFramedDiffeomorph.ofReverseNormal 2 (rightZeroDiffeomorph d 6 hd)
    (stabilizationAmbient m) (radialUnit m false) (sixColumnChange hd false) ?_ ?_
  · intro x
    calc
      _ = radialUnit m false + spatialIsometry m x.val.val := rightZeroEmbedding_apply d hd a x
      _ = radialUnit m false + stabilizationAmbient m (appendZeroMap (m + 1) 2 x.val.val) :=
        congrArg (fun w : Vector (2 + (m + 1)) ↦ radialUnit m false + w)
          (stabilizationAmbient_appendZero m x.val.val).symm
  · intro x v
    exact rightZeroFrame_apply d hd a y x v

end NoExoticSixSphere.CircleCylinder
