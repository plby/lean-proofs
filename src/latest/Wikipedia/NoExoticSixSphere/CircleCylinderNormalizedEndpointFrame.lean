import Wikipedia.NoExoticSixSphere.CircleCylinderOrderedEndpointFrame
import Wikipedia.NoExoticSixSphere.CollaredZeroComponentFrame

/-!
# Ordered normalization of the actual endpoint normal frames

The positive half-scale of the radial column disappears under
normalization. Its sign, its leading position, and every original tail
column are retained. The spatial inclusion is an actual linear isometry.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization Stiefel

theorem normalized_circlePrepend {m n : ℕ} {X : Type*} (left : Bool)
    (A : X → Vector (n + 1) →L[ℝ] Vector (m + 1)) (x : X) :
    Orthonormalization.operator (fun y ↦
      OrthogonalFramePrepend.operator ((1 / 2 : ℝ) • radialUnit m left)
        ((spatialIsometry m).toContinuousLinearMap.comp (A y))) x =
      OrthogonalFramePrepend.operator (radialUnit m left)
        ((spatialIsometry m).toContinuousLinearMap.comp (Orthonormalization.operator A x)) := by
  rw [OrthogonalFramePrepend.normalized_operator_pos_smul
    (radialUnit m left) (radialUnit_norm m left) (1 / 2) (by norm_num) _ x
      (fun v ↦ inner_radialUnit_spatialIsometry m left (A x v)),
    Orthonormalization.operator_comp_linearIsometry]

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem normalized_euclideanNormalFrame_left (a : Sphere 1 × Sphere m) (k : ℕ)
    (hd : m = n + k) (x : {x : Sphere m // d.leftMap x = b}) :
    letI := fiberAtlas d k hd;
    Orthonormalization.operator (euclideanNormalFrame d a k hd).ambient (leftInclusion d x) =
      (OrthogonalFramePrepend.operator (radialUnit m true)
        ((spatialIsometry m).toContinuousLinearMap.comp
          (Orthonormalization.operator (leftEndpointColumns d a.2 k hd) x))).comp
            (normalDimensionChange k hd).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  calc
    _ = Orthonormalization.operator (fun y ↦
        (OrthogonalFramePrepend.operator ((1 / 2 : ℝ) • radialUnit m true)
          ((spatialIsometry m).toContinuousLinearMap.comp (leftEndpointColumns d a.2 k hd y))).comp
            (normalDimensionChange k hd).toContinuousLinearMap) x :=
      Orthonormalization.operator_congr_value _ _ _ _
        (euclideanNormalFrame_left_ordered d a k hd x)
    _ = _ := by
      rw [normalDimensionChange, Orthonormalization.operator_comp_dimensionChange,
        normalized_circlePrepend]

theorem normalized_euclideanNormalFrame_right (a : Sphere 1 × Sphere m) (k : ℕ)
    (hd : m = n + k) (x : {x : Sphere m // d.rightMap x = b}) :
    letI := fiberAtlas d k hd;
    Orthonormalization.operator (euclideanNormalFrame d a k hd).ambient (rightInclusion d x) =
      (OrthogonalFramePrepend.operator (radialUnit m false)
        ((spatialIsometry m).toContinuousLinearMap.comp
          (Orthonormalization.operator (rightEndpointColumns d a.2 k hd) x))).comp
            (normalDimensionChange k hd).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  calc
    _ = Orthonormalization.operator (fun y ↦
        (OrthogonalFramePrepend.operator ((1 / 2 : ℝ) • radialUnit m false)
          ((spatialIsometry m).toContinuousLinearMap.comp (rightEndpointColumns d a.2 k hd y))).comp
            (normalDimensionChange k hd).toContinuousLinearMap) x :=
      Orthonormalization.operator_congr_value _ _ _ _
        (euclideanNormalFrame_right_ordered d a k hd x)
    _ = _ := by
      rw [normalDimensionChange, Orthonormalization.operator_comp_dimensionChange,
        normalized_circlePrepend]

end NoExoticSixSphere.CircleCylinder
