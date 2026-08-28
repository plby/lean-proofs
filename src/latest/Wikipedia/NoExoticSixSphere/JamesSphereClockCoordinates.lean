import Wikipedia.NoExoticSixSphere.JamesSphereMiddleSlice

/-!
# Finite stereographic coordinates of the middle slice and punctures

The actual clock is tangent compactification, not an unspecified circle
parameter. Its quarter, middle, and three-quarter values are respectively
-1, 0, and 1. Thus the chosen middle slice is the compactified coordinate
hyperplane and the two punctures are the corresponding finite axis points.
-/

noncomputable section

open scoped unitInterval OnePoint
open Wikipedia.HopfProblem.SixSphereCube

namespace NoExoticSixSphere.JamesSphere

def linePoint (r : ℝ) : CubicalProductSuspension.Line := WithLp.toLp 2 (fun _ ↦ r)

theorem clock_eq_coordinate (t : I) (ht₀ : 0 < (t : ℝ)) (ht₁ : (t : ℝ) < 1) :
    CubicalProductSuspension.clock t =
      (linePoint (SmoothInterval.coordinate (t : ℝ)) : OnePoint CubicalProductSuspension.Line) := by
  have hu : (fun _ : Fin 1 ↦ t) ∉ Cube.boundary (Fin 1) := by
    rintro ⟨i, hi⟩
    rcases hi with hi | hi
    · have he := congrArg Subtype.val hi
      change (t : ℝ) = 0 at he
      linarith
    · have he := congrArg Subtype.val hi
      change (t : ℝ) = 1 at he
      linarith
  change (euclideanOnePointSphere 1).symm
    (SmoothCube.compactification 1 (collapse (Cube.boundary (Fin 1)) (fun _ : Fin 1 ↦ t))) = _
  rw [collapse_of_not_mem _ hu]
  change (euclideanOnePointSphere 1).symm
    (euclideanOnePointSphere 1
      ((SmoothCube.interiorHomeomorph 1 ⟨fun _ : Fin 1 ↦ t, hu⟩) : OnePoint _)) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem clock_middleTime : CubicalProductSuspension.clock middleTime =
    ((0 : CubicalProductSuspension.Line) : OnePoint CubicalProductSuspension.Line) := by
  rw [clock_eq_coordinate middleTime (by norm_num [middleTime]) (by norm_num [middleTime])]
  congr 1
  ext i
  change Real.tan (Real.pi * ((1 : ℝ) / 2 - 1 / 2)) = 0
  norm_num

theorem clock_lowerTime : CubicalProductSuspension.clock lowerTime =
    (linePoint (-1) : OnePoint CubicalProductSuspension.Line) := by
  rw [clock_eq_coordinate lowerTime (by norm_num [lowerTime]) (by norm_num [lowerTime])]
  have he : SmoothInterval.coordinate (lowerTime : ℝ) = -1 := by
    change Real.tan (Real.pi * ((1 : ℝ) / 4 - 1 / 2)) = -1
    have ha : Real.pi * ((1 : ℝ) / 4 - 1 / 2) = -(Real.pi / 4) := by ring
    rw [ha, Real.tan_neg, Real.tan_pi_div_four]
  rw [he]

theorem clock_upperTime : CubicalProductSuspension.clock upperTime =
    (linePoint 1 : OnePoint CubicalProductSuspension.Line) := by
  rw [clock_eq_coordinate upperTime (by norm_num [upperTime]) (by norm_num [upperTime])]
  have he : SmoothInterval.coordinate (upperTime : ℝ) = 1 := by
    change Real.tan (Real.pi * ((3 : ℝ) / 4 - 1 / 2)) = 1
    have ha : Real.pi * ((3 : ℝ) / 4 - 1 / 2) = Real.pi / 4 := by ring
    rw [ha, Real.tan_pi_div_four]
  rw [he]

theorem compactification_zero (n : ℕ) :
    euclideanOnePointSphere n ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint _) = -spherePole n := by
  rw [euclideanOnePointSphere_coe]
  exact EuclideanSphere.stereographic'_symm_zero (spherePole n)

theorem middle_finite (n : ℕ) (a : EuclideanSpace ℝ (Fin n)) :
    middle n (euclideanOnePointSphere n (a : OnePoint _)) =
      euclideanOnePointSphere (n + 1)
        ((EuclideanFactorProduct.productCoordinates n 1 (a, 0)) : OnePoint _) := by
  change euclideanOnePointSphere (n + 1)
    ((EuclideanFactorProduct.productCoordinates n 1).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm
        (euclideanOnePointSphere n (a : OnePoint _)),
          CubicalProductSuspension.clock middleTime))) = _
  rw [Homeomorph.symm_apply_apply, clock_middleTime, OnePointProduct.map_coe]
  rfl

theorem lowerPuncture_finite (n : ℕ) :
    lowerPuncture n = euclideanOnePointSphere (n + 1)
      ((EuclideanFactorProduct.productCoordinates n 1 (0, linePoint (-1))) : OnePoint _) := by
  change euclideanOnePointSphere (n + 1)
    ((EuclideanFactorProduct.productCoordinates n 1).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm (-spherePole n),
        CubicalProductSuspension.clock lowerTime))) = _
  rw [← compactification_zero n, Homeomorph.symm_apply_apply, clock_lowerTime,
    OnePointProduct.map_coe]
  rfl

theorem upperPuncture_finite (n : ℕ) :
    upperPuncture n = euclideanOnePointSphere (n + 1)
      ((EuclideanFactorProduct.productCoordinates n 1 (0, linePoint 1)) : OnePoint _) := by
  change euclideanOnePointSphere (n + 1)
    ((EuclideanFactorProduct.productCoordinates n 1).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm (-spherePole n),
        CubicalProductSuspension.clock upperTime))) = _
  rw [← compactification_zero n, Homeomorph.symm_apply_apply, clock_upperTime,
    OnePointProduct.map_coe]
  rfl

end NoExoticSixSphere.JamesSphere
