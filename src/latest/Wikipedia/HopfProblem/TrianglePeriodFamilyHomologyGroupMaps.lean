import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyGroups

/-!
# Actual fibre and boundary maps in the finite integral markings

The finite coordinate equivalences keep the actual fibre image in the
first coordinate. Their remaining blocks are the marked, actual
Mayer--Vietoris connecting projection. These statements retain the maps
needed for later attachments, rather than merely computing group ranks.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology HomologyDifference
open TrianglePeriodFamilyHomologyFreeCoordinates

variable (D : Data ℂ TriangleRegularPoint)

private theorem integerFiveZero (z : ℤ) :
    integerFreeCoordinateEquiv 5 (z, 0) = ![z, 0, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> rfl

/-- The literal fibre map on first homology occupies the first integral coordinate. -/
@[simp] theorem familyH1Equiv_fibre (a : SingularHomology RealTorus₄ 1) :
    familyH1Equiv D
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 1 a) =
      ![FlatTorus.singularH1Equiv a 0, 0, 0] := by
  change integerFreeCoordinateEquiv 2
    ((familyH1ProductEquiv D _).1,
      (LinearEquiv.finTwoArrow ℤ ℤ).symm (familyH1ProductEquiv D _).2) = _
  rw [familyH1ProductEquiv_fibre]
  funext i
  fin_cases i <;> rfl

/-- The primitive integral degree-two fibre functional is the first coordinate. -/
@[simp] theorem familyH2Equiv_fibre (a : SingularHomology RealTorus₄ 2) :
    familyH2Equiv D
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 2 a) =
      ![6 * FlatTorus.singularH2Coordinates a 2 + FlatTorus.singularH2Coordinates a 3,
        0, 0, 0, 0, 0] := by
  change integerFreeCoordinateEquiv 5 (familyH2ProductEquiv D _) = _
  rw [familyH2ProductEquiv_fibre]
  exact integerFiveZero _

/-- The actual degree-three fibre map in the full finite marking. -/
@[simp] theorem familyH3Equiv_fibre (a : SingularHomology RealTorus₄ 3) :
    familyH3Equiv D
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 3 a) =
      ![FlatTorus.singularH3Coordinates a 0, 0, 0, 0, 0, 0, 0, 0] := by
  change integerFreeCoordinateEquiv 7 (familyH3ProductEquiv D _) = _
  rw [familyH3ProductEquiv_fibre]
  funext i
  fin_cases i <;> rfl

/-- The top fibre coordinate survives positively as the first degree-four coordinate. -/
@[simp] theorem familyH4Equiv_fibre (a : SingularHomology RealTorus₄ 4) :
    familyH4Equiv D
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 4 a) =
      ![realTorusH4Equiv a, 0, 0, 0, 0, 0] := by
  change integerFreeCoordinateEquiv 5 (familyH4ProductEquiv D _) = _
  rw [familyH4ProductEquiv_fibre]
  exact integerFiveZero _

/-- The last five degree-two coordinates are the actual boundary in its kernel marking. -/
theorem familyH2Equiv_tail (a : SingularHomology D.Space 2) (i : Fin 5) :
    familyH2Equiv D a (Fin.natAdd 1 i) = kernelOneEquiv (sourceKernelProjection D 1 a) i := by
  change integerFreeCoordinateEquiv 5 (familyH2ProductEquiv D a) (Fin.natAdd 1 i) = _
  rw [integerFreeCoordinateEquiv_apply_tail, familyH2ProductEquiv_snd]

/-- The last seven degree-three coordinates are the actual boundary in its kernel marking. -/
theorem familyH3Equiv_tail (a : SingularHomology D.Space 3) (i : Fin 7) :
    familyH3Equiv D a (Fin.natAdd 1 i) = kernelTwoEquiv (sourceKernelProjection D 2 a) i := by
  change integerFreeCoordinateEquiv 7 (familyH3ProductEquiv D a) (Fin.natAdd 1 i) = _
  rw [integerFreeCoordinateEquiv_apply_tail, familyH3ProductEquiv_snd]

/-- The last five degree-four coordinates are the actual boundary in its kernel marking. -/
theorem familyH4Equiv_tail (a : SingularHomology D.Space 4) (i : Fin 5) :
    familyH4Equiv D a (Fin.natAdd 1 i) = kernelThreeEquiv (sourceKernelProjection D 3 a) i := by
  change integerFreeCoordinateEquiv 5 (familyH4ProductEquiv D a) (Fin.natAdd 1 i) = _
  rw [integerFreeCoordinateEquiv_apply_tail, familyH4ProductEquiv_snd]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
