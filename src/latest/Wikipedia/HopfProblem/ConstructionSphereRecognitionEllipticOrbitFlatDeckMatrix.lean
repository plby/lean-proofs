import Wikipedia.HopfProblem.EllipticFlatTorus
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMatrixMaps

/-!
# The literal affine matrix after forgetting only the delta coordinate

The first three rows of the original four-dimensional monodromy have
zero last column.  Their original three-by-three submatrices therefore
act on the first three circle coordinates, retaining the couplings to
gamma and the projected native twist.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbitFlat

open Elliptic PeriodTorusHigherHomology

/-- The first three rows and columns of the original integral monodromy. -/
def projectedMatrix (j : Kind) : Matrix (Fin 3) (Fin 3) ℤ :=
  j.matrix.submatrix Fin.castSucc Fin.castSucc

theorem projectedMatrix_three :
    projectedMatrix .three = !![1, 0, 0; 6, 0, 1; -6, -1, -1] := by decide

theorem projectedMatrix_four :
    projectedMatrix .four = !![1, 0, 0; 0, 0, -1; -6, 1, 0] := by decide

/-- Only the fourth coordinate is omitted from the original native twist. -/
def projectedTwist (j : Kind) : Fin 3 → ℤ :=
  fun i => j.twist i.castSucc

theorem projectedTwist_three : projectedTwist .three = ![1, 2, -4] := by decide

theorem projectedTwist_four : projectedTwist .four = ![-1, -3, 3] := by decide

/-- The exact real translation is the projected native twist divided by its order. -/
def projectedTranslation (j : Kind) : Fin 3 → ℝ :=
  (1 / (j.order : ℝ)) • (fun i => (projectedTwist j i : ℝ))

theorem projectedTranslation_three :
    projectedTranslation .three = ![(1 : ℝ) / 3, 2 / 3, -4 / 3] := by
  ext i
  fin_cases i <;> norm_num [projectedTranslation, projectedTwist, Kind.order, Kind.twist, ε]

theorem projectedTranslation_four :
    projectedTranslation .four = ![(-1 : ℝ) / 4, -3 / 4, 3 / 4] := by
  ext i
  fin_cases i <;> norm_num [projectedTranslation, projectedTwist, Kind.order, Kind.twist, ε']

/-- The original first three rows have no dependence on the fourth coordinate. -/
theorem matrix_castSucc_last (j : Kind) (i : Fin 3) :
    j.matrix i.castSucc (Fin.last 3) = 0 := by
  cases j <;> fin_cases i <;> decide

/-- Restricting the original real linear map gives precisely this submatrix. -/
theorem prefix_flatLinear (j : Kind) (a : RealCoordinates) :
    (fun i : Fin 3 => flatLinear j a i.castSucc) =
      (projectedMatrix j).map (Int.castRingHom ℝ) *ᵥ (fun i => a i.castSucc) := by
  funext i
  change (∑ k : Fin 4, (j.matrix i.castSucc k : ℝ) * a k) =
    ∑ k : Fin 3, (j.matrix i.castSucc k.castSucc : ℝ) * a k.castSucc
  rw [Fin.sum_univ_castSucc]
  simp only [matrix_castSucc_last, Int.cast_zero, zero_mul, add_zero]

/-- The actual real affine formula on the first three coordinates. -/
def projectedRealAffine (j : Kind) (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (projectedMatrix j).map (Int.castRingHom ℝ) *ᵥ a + projectedTranslation j

theorem prefix_flatAffine (j : Kind) (a : RealCoordinates) :
    (fun i : Fin 3 => flatAffine j j.twist a i.castSucc) =
      projectedRealAffine j (fun i => a i.castSucc) := by
  change (fun i : Fin 3 => flatLinear j a i.castSucc) + projectedTranslation j = _
  rw [prefix_flatLinear]
  rfl

theorem projectedRealAffine_three (a : Fin 3 → ℝ) :
    projectedRealAffine .three a =
      ![a 0 + 1 / 3, 6 * a 0 + a 2 + 2 / 3, -6 * a 0 - a 1 - a 2 - 4 / 3] := by
  rw [projectedRealAffine, projectedMatrix_three, projectedTranslation_three]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem projectedRealAffine_four (a : Fin 3 → ℝ) :
    projectedRealAffine .four a =
      ![a 0 - 1 / 4, -a 2 - 3 / 4, -6 * a 0 + a 1 + 3 / 4] := by
  rw [projectedRealAffine, projectedMatrix_four, projectedTranslation_four]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The affine map on the actual product of the first three additive circles. -/
def projectedAffine (j : Kind) (x : ProductTorus 3) : ProductTorus 3 :=
  torusMatrixLinearMap (projectedMatrix j) x + coordinateProjection 3 (projectedTranslation j)

theorem projectedAffine_continuous (j : Kind) : Continuous (projectedAffine j) :=
  (torusMatrixLinearMap_continuous (projectedMatrix j)).add continuous_const

/-- The circle-product affine map descends the literal real affine formula. -/
theorem projectedAffine_coordinateProjection (j : Kind) (a : Fin 3 → ℝ) :
    projectedAffine j (coordinateProjection 3 a) =
      coordinateProjection 3 (projectedRealAffine j a) := by
  change torusMatrixMap (projectedMatrix j) (coordinateProjection 3 a) +
    coordinateProjection 3 (projectedTranslation j) = _
  rw [torusMatrixMap_coordinateProjection, projectedRealAffine, map_add]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbitFlat
