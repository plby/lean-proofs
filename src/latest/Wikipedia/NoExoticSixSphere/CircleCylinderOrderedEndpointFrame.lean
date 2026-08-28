import Wikipedia.NoExoticSixSphere.CircleCylinderEndpointFrameBlocks
import Wikipedia.NoExoticSixSphere.CircleCylinderNormalSourceCoordinates
import Wikipedia.NoExoticSixSphere.CircleCylinderSpatialCoordinates
import Wikipedia.NoExoticSixSphere.OrthogonalFramePrepend

/-!
# The actual endpoint frames in their original ordered Euclidean columns

The circle radial column is first, followed by the original endpoint
normal columns. The only source transport is the literal dimension-change
isometry already present in the circle double's normal coordinates.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization

theorem circleBlock_prepend {m n : ℕ} (left : Bool)
    (A : WithLp 2 (ℝ × Vector n) →L[ℝ] Vector (m + 1)) :
    ((ambientCoordinates m).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (HilbertProduct.map (circleNormal (SphereCylinder.endPole 0 left)) A)).comp
        (twoNormalCoordinates n).toContinuousLinearMap =
      OrthogonalFramePrepend.operator ((1 / 2 : ℝ) • radialUnit m left)
        ((spatialIsometry m).toContinuousLinearMap.comp
          (A.comp (endpointNormalCoordinates n).toContinuousLinearMap)) := by
  apply ContinuousLinearMap.ext
  intro v
  change ambientCoordinates m (WithLp.toLp 2
      (circleNormal (SphereCylinder.endPole 0 left) (v 0),
        A (endpointNormalCoordinates n (WithLp.toLp 2 (fun i ↦ v i.succ))))) =
    v 0 • ((1 / 2 : ℝ) • ambientCoordinates m
      (WithLp.toLp 2 ((SphereCylinder.endPole 0 left).val, (0 : Vector (m + 1))))) +
    ambientCoordinates m (WithLp.toLp 2 ((0 : V),
      A (endpointNormalCoordinates n (WithLp.toLp 2 (fun i ↦ v i.succ)))))
  rw [circleNormal_apply, smul_smul, ← map_smul, ← map_add]
  congr 1
  apply WithLp.ofLp_injective
  change ((v 0 / 2) • (SphereCylinder.endPole 0 left).val, _) =
    (v 0 * (1 / 2 : ℝ)) • ((SphereCylinder.endPole 0 left).val, (0 : Vector (m + 1))) +
      ((0 : V), _)
  simp [div_eq_mul_inv]

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def leftEndpointColumns (a : Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.leftMap x = b}) :
    Vector (n + 1) →L[ℝ] Vector (m + 1) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  exact ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b d.regular_left k hd a
    ).ambient x).comp (endpointNormalCoordinates n).toContinuousLinearMap

def rightEndpointColumns (a : Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.rightMap x = b}) :
    Vector (n + 1) →L[ℝ] Vector (m + 1) := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  exact ((SphereFiberNormalFrame.normalFrame d.rightMap d.smooth_right b d.regular_right k hd a
    ).ambient x).comp (endpointNormalCoordinates n).toContinuousLinearMap

theorem euclideanNormalFrame_left_ordered (a : Sphere 1 × Sphere m) (k : ℕ)
    (hd : m = n + k) (x : {x : Sphere m // d.leftMap x = b}) :
    letI := fiberAtlas d k hd;
    (euclideanNormalFrame d a k hd).ambient (leftInclusion d x) =
      (OrthogonalFramePrepend.operator ((1 / 2 : ℝ) • radialUnit m true)
        ((spatialIsometry m).toContinuousLinearMap.comp (leftEndpointColumns d a.2 k hd x))).comp
          (normalDimensionChange k hd).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [euclideanNormalFrame_left, normalCoordinates_factor]
  exact congrArg (fun L : Vector ((n + 1) + 1) →L[ℝ] Vector (2 + (m + 1)) ↦
    L.comp (normalDimensionChange k hd).toContinuousLinearMap)
      (circleBlock_prepend true
        ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b d.regular_left k hd a.2
          ).ambient x))

theorem euclideanNormalFrame_right_ordered (a : Sphere 1 × Sphere m) (k : ℕ)
    (hd : m = n + k) (x : {x : Sphere m // d.rightMap x = b}) :
    letI := fiberAtlas d k hd;
    (euclideanNormalFrame d a k hd).ambient (rightInclusion d x) =
      (OrthogonalFramePrepend.operator ((1 / 2 : ℝ) • radialUnit m false)
        ((spatialIsometry m).toContinuousLinearMap.comp (rightEndpointColumns d a.2 k hd x))).comp
          (normalDimensionChange k hd).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  rw [euclideanNormalFrame_right, normalCoordinates_factor]
  exact congrArg (fun L : Vector ((n + 1) + 1) →L[ℝ] Vector (2 + (m + 1)) ↦
    L.comp (normalDimensionChange k hd).toContinuousLinearMap)
      (circleBlock_prepend false
        ((SphereFiberNormalFrame.normalFrame d.rightMap d.smooth_right b d.regular_right k hd a.2
          ).ambient x))

end NoExoticSixSphere.CircleCylinder
