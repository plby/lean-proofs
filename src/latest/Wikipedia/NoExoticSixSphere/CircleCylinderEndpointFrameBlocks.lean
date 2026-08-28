import Wikipedia.NoExoticSixSphere.CircleCylinderEndpointEquations
import Wikipedia.NoExoticSixSphere.CircleCylinderFrameCoordinates

/-!
# The full original normal-frame blocks at both ends of the circle double

The actual endpoint equation germs give the entire canonical normal
operator: the signed radial circle column and the original endpoint
normal frame. The fixed ambient and normal coordinates retain this exact
block identity for the Euclidean frame used by the collared state.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem ambientNormalFrame_left (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.leftMap x = b}) :
    letI := fiberAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (ambientNormalFrame d a k hd).ambient (leftInclusion d x) =
      HilbertProduct.map (circleNormal (SphereCylinder.endPole 0 true))
        ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b d.regular_left k hd a.2
          ).ambient x) := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [ambientNormalFrame_ambient, fderiv_ambientEquations_left,
    orthogonalRightInverse_product _ _ (surjective_fderiv_circleNorm _)
      (SphereFiberNormalFrame.surjective_fderiv_equations d.leftMap d.smooth_left b a.2 x.val
        x.property (d.regular_left x.val x.property)),
    orthogonalRightInverse_circleNorm, SphereFiberNormalFrame.normalFrame_ambient]

theorem ambientNormalFrame_right (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.rightMap x = b}) :
    letI := fiberAtlas d k hd;
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    (ambientNormalFrame d a k hd).ambient (rightInclusion d x) =
      HilbertProduct.map (circleNormal (SphereCylinder.endPole 0 false))
        ((SphereFiberNormalFrame.normalFrame d.rightMap d.smooth_right b d.regular_right k hd a.2
          ).ambient x) := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  rw [ambientNormalFrame_ambient, fderiv_ambientEquations_right,
    orthogonalRightInverse_product _ _ (surjective_fderiv_circleNorm _)
      (SphereFiberNormalFrame.surjective_fderiv_equations d.rightMap d.smooth_right b a.2 x.val
        x.property (d.regular_right x.val x.property)),
    orthogonalRightInverse_circleNorm, SphereFiberNormalFrame.normalFrame_ambient]

theorem euclideanNormalFrame_left (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.leftMap x = b}) :
    letI := fiberAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (euclideanNormalFrame d a k hd).ambient (leftInclusion d x) =
      ((ambientCoordinates m).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (HilbertProduct.map (circleNormal (SphereCylinder.endPole 0 true))
          ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b d.regular_left k hd a.2
            ).ambient x))).comp (normalCoordinates k hd).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [euclideanNormalFrame_from_ambient, ambientNormalFrame_left]

theorem euclideanNormalFrame_right (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.rightMap x = b}) :
    letI := fiberAtlas d k hd;
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    (euclideanNormalFrame d a k hd).ambient (rightInclusion d x) =
      ((ambientCoordinates m).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (HilbertProduct.map (circleNormal (SphereCylinder.endPole 0 false))
          ((SphereFiberNormalFrame.normalFrame d.rightMap d.smooth_right b d.regular_right k hd a.2
            ).ambient x))).comp (normalCoordinates k hd).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  rw [euclideanNormalFrame_from_ambient, ambientNormalFrame_right]

end NoExoticSixSphere.CircleCylinder
