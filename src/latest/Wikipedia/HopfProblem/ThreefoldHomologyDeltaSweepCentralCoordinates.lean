import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepCentralCoordinatesTransfer

/-!
# The central delta sweep in the unchanged Wang markings

The actual sweep forces divisibility of the genuine second covering shear.
Its marked matrix has first column zero and second column `(-b / N, -1)`.
The second source basis vector remains the original chosen Wang section;
it is not replaced by the literal positive base circle. The negative sweep
of that basis vector gives a native global-kernel class with second
coordinate one.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open Elliptic Elliptic.HigherHomology EllipticFilling SingularMayerVietoris
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang

/-- The second coordinate is fixed by the positive delta-left product
orientation, independently of the chosen Wang splitting. -/
theorem centralSweep_secondCoordinate (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 1) :
    surfaceH2Equiv j (specialLocalData j).centralPeriod (centralSweep j 1 a) 1 =
      -surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 := by
  apply mul_right_cancel₀ (show j.twist 0 ≠ 0 by cases j <;> decide)
  have h := congrFun (centralSweep_h2Coordinates j a) (2 : Fin 6)
  rw [h2Coordinates_formula] at h
  simpa [fibreInvariantPairVector, twistDeltaVector] using h

/-- The first coordinate retains the actual second covering shear, with
its genuine one-or-two norm index. -/
theorem centralSweep_firstCoordinate_mul_index (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 1) :
    (fibreNormIndex j : ℤ) *
        surfaceH2Equiv j (specialLocalData j).centralPeriod (centralSweep j 1 a) 0 =
      -sourceShearTwo j * surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 := by
  have h := congrFun (centralSweep_h2Coordinates j a) (3 : Fin 6)
  rw [h2Coordinates_formula] at h
  have hzero :
      ((fibreNormIndex j : ℤ) *
          surfaceH2Equiv j (specialLocalData j).centralPeriod (centralSweep j 1 a) 0 -
        sourceShearTwo j *
          surfaceH2Equiv j (specialLocalData j).centralPeriod (centralSweep j 1 a) 1) *
        fibreSquareKernelVector j 0 = 0 := by
    simpa [fibreInvariantPairVector, twistDeltaVector] using h
  have hcoef := (mul_eq_zero.mp hzero).resolve_right
    (show fibreSquareKernelVector j 0 ≠ 0 by cases j <;> decide)
  rw [centralSweep_secondCoordinate] at hcoef
  linarith only [hcoef]

/-- Divisibility of the frozen, geometrically defined second covering
shear is a consequence of the actual integral sweep. -/
theorem fibreNormIndex_dvd_sourceShearTwo (j : Kind) :
    (fibreNormIndex j : ℤ) ∣ sourceShearTwo j := by
  let a := (surfaceH1Equiv j (specialLocalData j).centralPeriod).symm ![0, 1]
  have h := centralSweep_firstCoordinate_mul_index j a
  have ha : surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 = 1 := by
    simp [a]
  rw [ha, mul_one] at h
  refine ⟨-surfaceH2Equiv j (specialLocalData j).centralPeriod (centralSweep j 1 a) 0, ?_⟩
  rw [mul_neg, h, neg_neg]

/-- In particular, the genuine order-four covering shear is even. -/
theorem two_dvd_sourceShearTwo_four : (2 : ℤ) ∣ sourceShearTwo .four := by
  simpa using fibreNormIndex_dvd_sourceShearTwo Kind.four

/-- The integral correction determined by the original second covering
shear, without changing either surface marking. -/
def centralSweepShearCorrection (j : Kind) : ℤ :=
  sourceShearTwo j / (fibreNormIndex j : ℤ)

theorem fibreNormIndex_mul_centralSweepShearCorrection (j : Kind) :
    (fibreNormIndex j : ℤ) * centralSweepShearCorrection j = sourceShearTwo j := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (fibreNormIndex_dvd_sourceShearTwo j)

theorem centralSweep_firstCoordinate (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 1) :
    surfaceH2Equiv j (specialLocalData j).centralPeriod (centralSweep j 1 a) 0 =
      -centralSweepShearCorrection j *
        surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 := by
  apply mul_left_cancel₀ (fibreNormIndex_int_ne_zero j)
  rw [centralSweep_firstCoordinate_mul_index,
    ← fibreNormIndex_mul_centralSweepShearCorrection]
  ring

/-- The complete genuine sweep formula in the original chosen Wang
markings, including the derived integral shear correction. -/
theorem centralSweep_coordinates (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 1) :
    surfaceH2Equiv j (specialLocalData j).centralPeriod (centralSweep j 1 a) =
      ![-centralSweepShearCorrection j *
          surfaceH1Equiv j (specialLocalData j).centralPeriod a 1,
        -surfaceH1Equiv j (specialLocalData j).centralPeriod a 1] := by
  ext i
  fin_cases i
  · exact centralSweep_firstCoordinate j a
  · exact centralSweep_secondCoordinate j a

/-- The actual two-by-two marked matrix, with no basis change. -/
theorem centralSweep_matrix (j : Kind) (v : Fin 2 → ℤ) :
    surfaceH2Equiv j (specialLocalData j).centralPeriod
        (centralSweep j 1 ((surfaceH1Equiv j (specialLocalData j).centralPeriod).symm v)) =
      !![0, -centralSweepShearCorrection j; 0, -1] *ᵥ v := by
  rw [centralSweep_coordinates, LinearEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The old first Wang basis vector has zero genuine sweep. -/
theorem centralSweep_first_axis (j : Kind) :
    centralSweep j 1
      ((surfaceH1Equiv j (specialLocalData j).centralPeriod).symm ![1, 0]) = 0 := by
  apply (surfaceH2Equiv j (specialLocalData j).centralPeriod).injective
  rw [centralSweep_coordinates, LinearEquiv.apply_symm_apply, map_zero]
  simp

/-- The negative sweep of the original second Wang basis vector has
second coordinate one, with its first coordinate forced by the actual shear. -/
theorem neg_centralSweep_second_axis_coordinates (j : Kind) :
    surfaceH2Equiv j (specialLocalData j).centralPeriod
        (-centralSweep j 1
          ((surfaceH1Equiv j (specialLocalData j).centralPeriod).symm ![0, 1])) =
      ![centralSweepShearCorrection j, 1] := by
  rw [map_neg, centralSweep_coordinates, LinearEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> simp

/-- This same native class lies in the kernel of the original central
inclusion on global second homology. -/
theorem neg_centralSweep_second_axis_global_eq_zero (j : Kind) :
    singularHomologyMap (centralInclusionMap j) 2
        (-centralSweep j 1
          ((surfaceH1Equiv j (specialLocalData j).centralPeriod).symm ![0, 1])) = 0 := by
  rw [map_neg, centralSweep_global_eq_zero, neg_zero]

/-- An actual global-kernel class with unit second coordinate, derived
from the original circle action and the unchanged Wang markings. -/
theorem exists_centralKernelClass_unit_secondCoordinate (j : Kind) :
    ∃ a : SingularHomology (SpecialCentralSurface j) 2,
      surfaceH2Equiv j (specialLocalData j).centralPeriod a =
          ![centralSweepShearCorrection j, 1] ∧
        singularHomologyMap (centralInclusionMap j) 2 a = 0 :=
  ⟨-centralSweep j 1
      ((surfaceH1Equiv j (specialLocalData j).centralPeriod).symm ![0, 1]),
    neg_centralSweep_second_axis_coordinates j,
    neg_centralSweep_second_axis_global_eq_zero j⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
