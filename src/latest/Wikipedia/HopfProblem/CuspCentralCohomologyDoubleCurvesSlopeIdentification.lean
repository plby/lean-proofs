import Wikipedia.HopfProblem.CuspCentralCohomologyDoubleCurvesPure
import Wikipedia.HopfProblem.CuspCentralCohomologySlopeForm

/-!
# Identifying native slope classes from actual mixed evaluations

The original ordered-minor marking determines a native degree-two class
from its two pure coordinates and its four canonical mixed evaluations.
The proved sign of the slope evaluation therefore identifies a class
whose mixed evaluations are `c ν(B₀β)ν(v)` with `(-c) • slopeClass a b`.

This is a uniqueness statement about native singular cohomology.  It
does not assume that any particular geometric curve has these mixed
evaluations; that geometric calculation is supplied separately.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

/-- The four canonical mixed unit pairs are exactly the four middle
positions in the original ordered-minor marking. -/
theorem mixedPeriodCoordinates_single_single (i j : Fin 2) :
    mixedPeriodCoordinates (Pi.single i 1) (Pi.single j 1) =
      Pi.single (![![1, 2], ![3, 4]] i j : Fin 6) 1 := by
  fin_cases i <;> fin_cases j <;> funext k <;> fin_cases k <;>
    simp [mixedPeriodCoordinates]

/-- Pure coordinates and the four actual mixed basis evaluations
determine a class of the native singular cochain cohomology. -/
theorem eq_of_pure_coordinates_and_mixed_basis_evaluate
    (A D : SingularCohomology (ProductTorus 4) 2)
    (hzero : coordinateTorusH2CohomologyCoordinates A 0 =
      coordinateTorusH2CohomologyCoordinates D 0)
    (hfive : coordinateTorusH2CohomologyCoordinates A 5 =
      coordinateTorusH2CohomologyCoordinates D 5)
    (hmixed : ∀ i j : Fin 2,
      singularEvaluation (ProductTorus 4) 2 A
          (coordinateTorusH2Coordinates.symm
            (mixedPeriodCoordinates (Pi.single i 1) (Pi.single j 1))) =
        singularEvaluation (ProductTorus 4) 2 D
          (coordinateTorusH2Coordinates.symm
            (mixedPeriodCoordinates (Pi.single i 1) (Pi.single j 1)))) :
    A = D := by
  have hmiddle (i j : Fin 2) :
      coordinateTorusH2CohomologyCoordinates A (![![1, 2], ![3, 4]] i j : Fin 6) =
        coordinateTorusH2CohomologyCoordinates D (![![1, 2], ![3, 4]] i j : Fin 6) := by
    have h := hmixed i j
    rw [mixedPeriodCoordinates_single_single] at h
    simpa only [coordinateTorusH2CohomologyCoordinates,
      coordinateTorusCohomologyCoordinates_apply_coordinate] using h
  apply coordinateTorusH2CohomologyCoordinates.injective
  funext k
  fin_cases k
  · exact hzero
  · exact hmiddle 0 0
  · exact hmiddle 0 1
  · exact hmiddle 1 0
  · exact hmiddle 1 1
  · exact hfive

/-- Multiplying the existing signed slope evaluation by `-c` gives the
positive product with coefficient `c`, with no new lattice identification. -/
theorem neg_smul_slopeClass_evaluate_mixedCoordinates_B₀
    (a b c : ℤ) (β v : Fin 2 → ℤ) :
    singularEvaluation (ProductTorus 4) 2 ((-c) • slopeClass a b)
        (coordinateTorusH2Coordinates.symm (mixedPeriodCoordinates β v)) =
      c * (a * (B₀ *ᵥ β) 0 + b * (B₀ *ᵥ β) 1) * (a * v 0 + b * v 1) := by
  simp only [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, Int.cast_id,
    slopeClass_evaluate_mixedCoordinates_B₀]
  ring

/-- Four canonical mixed tests and the two pure vanishings suffice to
identify the actual native class, including its integral sign. -/
theorem eq_neg_smul_slopeClass_of_mixed_basis_evaluate
    (A : SingularCohomology (ProductTorus 4) 2) (a b c : ℤ)
    (hzero : coordinateTorusH2CohomologyCoordinates A 0 = 0)
    (hfive : coordinateTorusH2CohomologyCoordinates A 5 = 0)
    (hmixed : ∀ i j : Fin 2,
      singularEvaluation (ProductTorus 4) 2 A
          (coordinateTorusH2Coordinates.symm
            (mixedPeriodCoordinates (Pi.single i 1) (Pi.single j 1))) =
        c * (a * (B₀ *ᵥ (Pi.single i 1)) 0 + b * (B₀ *ᵥ (Pi.single i 1)) 1) *
          (a * (Pi.single j 1 : Fin 2 → ℤ) 0 + b * (Pi.single j 1 : Fin 2 → ℤ) 1)) :
    A = (-c) • slopeClass a b := by
  apply eq_of_pure_coordinates_and_mixed_basis_evaluate A ((-c) • slopeClass a b)
  · rw [map_zsmul, slopeClass_coordinates]
    simpa [slopeCoefficients] using hzero
  · rw [map_zsmul, slopeClass_coordinates]
    simpa [slopeCoefficients] using hfive
  · intro i j
    rw [hmixed i j, neg_smul_slopeClass_evaluate_mixedCoordinates_B₀]

/-- The geometric mixed-evaluation formula uniquely determines the
native cohomology class once its two pure coefficients vanish. -/
theorem eq_neg_smul_slopeClass_of_mixed_evaluate
    (A : SingularCohomology (ProductTorus 4) 2) (a b c : ℤ)
    (hzero : coordinateTorusH2CohomologyCoordinates A 0 = 0)
    (hfive : coordinateTorusH2CohomologyCoordinates A 5 = 0)
    (hmixed : ∀ β v : Fin 2 → ℤ,
      singularEvaluation (ProductTorus 4) 2 A
          (coordinateTorusH2Coordinates.symm (mixedPeriodCoordinates β v)) =
        c * (a * (B₀ *ᵥ β) 0 + b * (B₀ *ᵥ β) 1) * (a * v 0 + b * v 1)) :
    A = (-c) • slopeClass a b :=
  eq_neg_smul_slopeClass_of_mixed_basis_evaluate A a b c hzero hfive
    (fun i j => hmixed (Pi.single i 1) (Pi.single j 1))

end Wikipedia.HopfProblem.CuspCentralCohomology
