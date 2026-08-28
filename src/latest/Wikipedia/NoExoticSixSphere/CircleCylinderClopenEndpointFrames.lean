import Wikipedia.NoExoticSixSphere.CircleCylinderClopenEndpoints
import Wikipedia.NoExoticSixSphere.CircleCylinderStateSixFrame
import Wikipedia.HopfProblem.DegreeCollapseClopenEmbedding

/-!
# The actual embeddings and induced frames on both native clopen endpoints

Restriction retains every original ambient point and normal column.
The previously proved affine point formulas and signed two-axis six-frame
identities therefore hold on the inherited clopen endpoint atlases.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hd : m = n + 6) (a : Sphere 1 × Sphere m)

def leftZeroEmbedding : letI := timeZeroAtlas d 6 hd;
    EuclideanEmbedding 6 (leftZeroOpen d 6 hd) := by
  let S := lowCollaredState d hd a
  let := S.zeroAtlas
  let := timeZeroAtlas d 6 hd
  exact ClopenEmbedding.restrict (CollaredZero.embedding (lowCollaredState d hd a))
    (leftZeroOpen d 6 hd) (leftZeroOpen_closed d 6 hd)

def rightZeroEmbedding : letI := timeZeroAtlas d 6 hd;
    EuclideanEmbedding 6 (rightZeroOpen d 6 hd) := by
  let S := lowCollaredState d hd a
  let := S.zeroAtlas
  let := timeZeroAtlas d 6 hd
  exact ClopenEmbedding.restrict (CollaredZero.embedding (lowCollaredState d hd a))
    (rightZeroOpen d 6 hd) (rightZeroOpen_closed d 6 hd)

def leftZeroFrame (y : Fiber d) : letI := timeZeroAtlas d 6 hd;
    SmoothRangeFrame (𝓡 6) (leftZeroEmbedding d hd a).normalProjection
      (leftZeroEmbedding d hd a).NormalModel := by
  let S := lowCollaredState d hd a
  let := S.zeroAtlas
  let := timeZeroAtlas d 6 hd
  exact ClopenEmbedding.restrictNormalFrame (CollaredZero.embedding (lowCollaredState d hd a))
    (leftZeroOpen d 6 hd) (leftZeroOpen_closed d 6 hd)
      (CollaredZero.normalFrame (lowCollaredState d hd a) y)

def rightZeroFrame (y : Fiber d) : letI := timeZeroAtlas d 6 hd;
    SmoothRangeFrame (𝓡 6) (rightZeroEmbedding d hd a).normalProjection
      (rightZeroEmbedding d hd a).NormalModel := by
  let S := lowCollaredState d hd a
  let := S.zeroAtlas
  let := timeZeroAtlas d 6 hd
  exact ClopenEmbedding.restrictNormalFrame (CollaredZero.embedding (lowCollaredState d hd a))
    (rightZeroOpen d 6 hd) (rightZeroOpen_closed d 6 hd)
      (CollaredZero.normalFrame (lowCollaredState d hd a) y)

theorem leftZeroEmbedding_apply (x : {x : Sphere m // d.leftMap x = b}) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := timeZeroAtlas d 6 hd;
    (leftZeroEmbedding d hd a).toFun (leftZeroDiffeomorph d 6 hd x) =
      radialUnit m true + spatialIsometry m x.val.val := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let S := lowCollaredState d hd a
  let := S.zeroAtlas
  let := timeZeroAtlas d 6 hd
  change (CollaredZero.embedding (lowCollaredState d hd a)).toFun
    (leftZeroDiffeomorph d 6 hd x).val = _
  rw [leftZeroDiffeomorph_val]
  exact lowState_embedding_left d hd a x

theorem rightZeroEmbedding_apply (x : {x : Sphere m // d.rightMap x = b}) :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd);
    letI := timeZeroAtlas d 6 hd;
    (rightZeroEmbedding d hd a).toFun (rightZeroDiffeomorph d 6 hd x) =
      radialUnit m false + spatialIsometry m x.val.val := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let S := lowCollaredState d hd a
  let := S.zeroAtlas
  let := timeZeroAtlas d 6 hd
  change (CollaredZero.embedding (lowCollaredState d hd a)).toFun
    (rightZeroDiffeomorph d 6 hd x).val = _
  rw [rightZeroDiffeomorph_val]
  exact lowState_embedding_right d hd a x

theorem leftZeroFrame_apply (y : Fiber d) (x : {x : Sphere m // d.leftMap x = b})
    (v : Vector (2 + (m + 1) - 6)) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := timeZeroAtlas d 6 hd;
    (leftZeroFrame d hd a y).ambient (leftZeroDiffeomorph d 6 hd x) v =
      stabilizationAmbient m
        (BlockSum.operator 2 (Orthonormalization.operator (N := m + 1) (n := m + 1 - 6)
          (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a.2).ambient x)
            (sixColumnChange hd true v)) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let S := lowCollaredState d hd a
  let := S.zeroAtlas
  let := timeZeroAtlas d 6 hd
  change (CollaredZero.normalFrame (lowCollaredState d hd a) y).ambient
    (leftZeroDiffeomorph d 6 hd x).val v = _
  rw [leftZeroDiffeomorph_val]
  exact lowState_sixFrame_left d hd a y x v

theorem rightZeroFrame_apply (y : Fiber d) (x : {x : Sphere m // d.rightMap x = b})
    (v : Vector (2 + (m + 1) - 6)) :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd);
    letI := timeZeroAtlas d 6 hd;
    (rightZeroFrame d hd a y).ambient (rightZeroDiffeomorph d 6 hd x) v =
      stabilizationAmbient m
        (BlockSum.operator 2 (Orthonormalization.operator (N := m + 1) (n := m + 1 - 6)
          (RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right 6 hd a.2).ambient x)
            (sixColumnChange hd false v)) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let S := lowCollaredState d hd a
  let := S.zeroAtlas
  let := timeZeroAtlas d 6 hd
  change (CollaredZero.normalFrame (lowCollaredState d hd a) y).ambient
    (rightZeroDiffeomorph d 6 hd x).val v = _
  rw [rightZeroDiffeomorph_val]
  exact lowState_sixFrame_right d hd a y x v

end NoExoticSixSphere.CircleCylinder
