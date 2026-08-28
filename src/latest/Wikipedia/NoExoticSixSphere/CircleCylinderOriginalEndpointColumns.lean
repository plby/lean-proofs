import Wikipedia.NoExoticSixSphere.CircleCylinderNormalizedEndpointFrame
import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding

/-!
# The ordered endpoint columns are the original regular-fiber frames

The original endpoint frame has its original normal dimension and native
atlas. The comparison is a literal dimension-change isometry, so ordered
normalization commutes with it. No arbitrary source-frame change is used.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization Stiefel

def endpointColumnChange {m n : ℕ} (k : ℕ) (hd : m = n + k) :
    Vector (n + 1) ≃ₗᵢ[ℝ] Vector (m + 1 - k) :=
  Orthonormalization.dimensionChange (by omega)

theorem originalNormalCoordinates_factor {m n : ℕ} (k : ℕ) (hd : m = n + k) :
    (endpointColumnChange k hd).toContinuousLinearEquiv.trans
      (RegularSphereFiber.normalCoordinates k hd) = endpointNormalCoordinates n := by
  have hf : RegularSphereFiber.normalCoordinates k hd =
      (Orthonormalization.dimensionChange (show m + 1 - k = n + 1 by omega)
        ).toContinuousLinearEquiv.trans (endpointNormalCoordinates n) := by
    unfold RegularSphereFiber.normalCoordinates
    exact cast_source_continuousLinearEquiv (by omega) (endpointNormalCoordinates n)
  rw [hf]
  apply ContinuousLinearEquiv.ext
  funext v
  change endpointNormalCoordinates n
    (Orthonormalization.dimensionChange (show m + 1 - k = n + 1 by omega)
      (Orthonormalization.dimensionChange (show n + 1 = m + 1 - k by omega) v)) =
    endpointNormalCoordinates n v
  apply congrArg (endpointNormalCoordinates n)
  ext i
  rfl

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem leftEndpointColumns_eq_originalFrame (a : Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.leftMap x = b}) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    leftEndpointColumns d a k hd x =
      ((RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left k hd a).ambient x).comp
        (endpointColumnChange k hd).toContinuousLinearMap := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  change ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b d.regular_left k hd a
    ).ambient x).comp (endpointNormalCoordinates n).toContinuousLinearMap = _
  rw [← originalNormalCoordinates_factor k hd]
  rfl

theorem rightEndpointColumns_eq_originalFrame (a : Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.rightMap x = b}) :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    rightEndpointColumns d a k hd x =
      ((RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right k hd a).ambient x).comp
        (endpointColumnChange k hd).toContinuousLinearMap := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  change ((SphereFiberNormalFrame.normalFrame d.rightMap d.smooth_right b d.regular_right k hd a
    ).ambient x).comp (endpointNormalCoordinates n).toContinuousLinearMap = _
  rw [← originalNormalCoordinates_factor k hd]
  rfl

theorem normalized_leftEndpointColumns (a : Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.leftMap x = b}) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    Orthonormalization.operator (leftEndpointColumns d a k hd) x =
      (Orthonormalization.operator
        (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left k hd a).ambient x).comp
          (endpointColumnChange k hd).toContinuousLinearMap := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  calc
    _ = Orthonormalization.operator (fun y ↦
        ((RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left k hd a
          ).ambient y).comp (endpointColumnChange k hd).toContinuousLinearMap) x :=
      Orthonormalization.operator_congr_value _ _ _ _
        (leftEndpointColumns_eq_originalFrame d a k hd x)
    _ = _ := Orthonormalization.operator_comp_dimensionChange
      (show n + 1 = m + 1 - k by omega) _ x

theorem normalized_rightEndpointColumns (a : Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.rightMap x = b}) :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    Orthonormalization.operator (rightEndpointColumns d a k hd) x =
      (Orthonormalization.operator
        (RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right k hd a
          ).ambient x).comp
          (endpointColumnChange k hd).toContinuousLinearMap := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  calc
    _ = Orthonormalization.operator (fun y ↦
        ((RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right k hd a
          ).ambient y).comp (endpointColumnChange k hd).toContinuousLinearMap) x :=
      Orthonormalization.operator_congr_value _ _ _ _
        (rightEndpointColumns_eq_originalFrame d a k hd x)
    _ = _ := Orthonormalization.operator_comp_dimensionChange
      (show n + 1 = m + 1 - k by omega) _ x

end NoExoticSixSphere.CircleCylinder
