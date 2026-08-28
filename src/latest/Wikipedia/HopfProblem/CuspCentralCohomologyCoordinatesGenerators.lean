import Wikipedia.HopfProblem.CuspCentralCohomologyCoordinatesFixed

/-!
# Actual native cohomology generators for the fixed submodules

The classes are defined in native singular cohomology by the inverse of
its proved evaluation coordinates.  They form actual integral bases and
evaluate as the coordinate-dual classes of the original homology marking.

The degree-one labels are `γ, u, w, δ`.  The degree-two labels are
`γu, γw, γδ, uw, uδ, wδ`, and the degree-three labels are
`γuw, γuδ, γwδ, uwδ`.  These labels name the evaluation-dual bases;
no cup-product identification is asserted here.

The fixed classes of the genuine pullback are precisely the displayed
integer linear combinations, including `γw - uδ` in degree two.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology
open CuspCentralHomology.SpecializationModel

/-- Native classes dual to the four original positive coordinate loops, labelled `γ,u,w,δ`. -/
def coordinateTorusH1DualClass (i : Fin 4) : SingularCohomology (ProductTorus 4) 1 :=
  coordinateTorusH1CohomologyCoordinates.symm (Pi.single i 1)

/-- Native classes in the ordered dual-minor basis `γu,γw,γδ,uw,uδ,wδ`. -/
def coordinateTorusH2DualClass (i : Fin 6) : SingularCohomology (ProductTorus 4) 2 :=
  coordinateTorusH2CohomologyCoordinates.symm (Pi.single i 1)

/-- Native classes in the ordered dual-minor basis `γuw,γuδ,γwδ,uwδ`. -/
def coordinateTorusH3DualClass (i : Fin 4) : SingularCohomology (ProductTorus 4) 3 :=
  coordinateTorusH3CohomologyCoordinates.symm (Pi.single i 1)

@[simp] theorem coordinateTorusH1DualClass_coordinates (i : Fin 4) :
    coordinateTorusH1CohomologyCoordinates (coordinateTorusH1DualClass i) = Pi.single i 1 :=
  coordinateTorusH1CohomologyCoordinates.apply_symm_apply _

@[simp] theorem coordinateTorusH2DualClass_coordinates (i : Fin 6) :
    coordinateTorusH2CohomologyCoordinates (coordinateTorusH2DualClass i) = Pi.single i 1 :=
  coordinateTorusH2CohomologyCoordinates.apply_symm_apply _

@[simp] theorem coordinateTorusH3DualClass_coordinates (i : Fin 4) :
    coordinateTorusH3CohomologyCoordinates (coordinateTorusH3DualClass i) = Pi.single i 1 :=
  coordinateTorusH3CohomologyCoordinates.apply_symm_apply _

/-- These native degree-one classes constitute an actual integral basis. -/
def coordinateTorusH1DualBasis :
    Module.Basis (Fin 4) ℤ (SingularCohomology (ProductTorus 4) 1) :=
  (Pi.basisFun ℤ (Fin 4)).map coordinateTorusH1CohomologyCoordinates.symm

/-- These native degree-two classes constitute an actual integral basis. -/
def coordinateTorusH2DualBasis :
    Module.Basis (Fin 6) ℤ (SingularCohomology (ProductTorus 4) 2) :=
  (Pi.basisFun ℤ (Fin 6)).map coordinateTorusH2CohomologyCoordinates.symm

/-- These native degree-three classes constitute an actual integral basis. -/
def coordinateTorusH3DualBasis :
    Module.Basis (Fin 4) ℤ (SingularCohomology (ProductTorus 4) 3) :=
  (Pi.basisFun ℤ (Fin 4)).map coordinateTorusH3CohomologyCoordinates.symm

@[simp] theorem coordinateTorusH1DualBasis_apply (i : Fin 4) :
    coordinateTorusH1DualBasis i = coordinateTorusH1DualClass i := by
  simp only [coordinateTorusH1DualBasis, Module.Basis.map_apply, Pi.basisFun_apply,
    coordinateTorusH1DualClass]

@[simp] theorem coordinateTorusH2DualBasis_apply (i : Fin 6) :
    coordinateTorusH2DualBasis i = coordinateTorusH2DualClass i := by
  simp only [coordinateTorusH2DualBasis, Module.Basis.map_apply, Pi.basisFun_apply,
    coordinateTorusH2DualClass]

@[simp] theorem coordinateTorusH3DualBasis_apply (i : Fin 4) :
    coordinateTorusH3DualBasis i = coordinateTorusH3DualClass i := by
  simp only [coordinateTorusH3DualBasis, Module.Basis.map_apply, Pi.basisFun_apply,
    coordinateTorusH3DualClass]

/-- Evaluation on every actual degree-one homology class gives its original coordinate. -/
theorem coordinateTorusH1DualClass_evaluate (i : Fin 4)
    (a : SingularHomology (ProductTorus 4) 1) :
    singularEvaluation (ProductTorus 4) 1 (coordinateTorusH1DualClass i) a =
      coordinateTorusH1Coordinates a i := by
  change singularEvaluation (ProductTorus 4) 1
    ((coordinateTorusCohomologyCoordinates 1 coordinateTorusH1Coordinates).symm
      (Pi.single i 1)) a = _
  rw [coordinateTorusCohomologyCoordinates_symm_evaluate]
  simp [Pi.single_apply]

/-- The degree-two dual class evaluates on the actual ordered-minor coordinate. -/
theorem coordinateTorusH2DualClass_evaluate (i : Fin 6)
    (a : SingularHomology (ProductTorus 4) 2) :
    singularEvaluation (ProductTorus 4) 2 (coordinateTorusH2DualClass i) a =
      coordinateTorusH2Coordinates a i := by
  change singularEvaluation (ProductTorus 4) 2
    ((coordinateTorusCohomologyCoordinates 2 coordinateTorusH2Coordinates).symm
      (Pi.single i 1)) a = _
  rw [coordinateTorusCohomologyCoordinates_symm_evaluate]
  simp [Pi.single_apply]

/-- The degree-three dual class evaluates on the actual ordered-minor coordinate. -/
theorem coordinateTorusH3DualClass_evaluate (i : Fin 4)
    (a : SingularHomology (ProductTorus 4) 3) :
    singularEvaluation (ProductTorus 4) 3 (coordinateTorusH3DualClass i) a =
      coordinateTorusH3Coordinates a i := by
  change singularEvaluation (ProductTorus 4) 3
    ((coordinateTorusCohomologyCoordinates 3 coordinateTorusH3Coordinates).symm
      (Pi.single i 1)) a = _
  rw [coordinateTorusCohomologyCoordinates_symm_evaluate]
  simp [Pi.single_apply]

theorem coordinateTorusH1_linearCombination_coordinates (a b : ℤ) :
    coordinateTorusH1CohomologyCoordinates
      (a • coordinateTorusH1DualClass 0 + b • coordinateTorusH1DualClass 1) =
      ![a, b, 0, 0] := by
  ext i
  fin_cases i <;> simp

theorem coordinateTorusH2_linearCombination_coordinates (a b c d : ℤ) :
    coordinateTorusH2CohomologyCoordinates
      (a • coordinateTorusH2DualClass 0 +
        b • (coordinateTorusH2DualClass 1 - coordinateTorusH2DualClass 4) +
        c • coordinateTorusH2DualClass 2 + d • coordinateTorusH2DualClass 3) =
      ![a, b, c, d, -b, 0] := by
  ext i
  fin_cases i <;> simp

theorem coordinateTorusH3_linearCombination_coordinates (a b : ℤ) :
    coordinateTorusH3CohomologyCoordinates
      (a • coordinateTorusH3DualClass 0 + b • coordinateTorusH3DualClass 1) =
      ![a, b, 0, 0] := by
  ext i
  fin_cases i <;> simp

/-- The previously constructed native section is the literal combination of its generators. -/
theorem coordinateTorusH1FixedSection_apply (z : Fin 2 → ℤ) :
    coordinateTorusH1FixedSection z =
      z 0 • coordinateTorusH1DualClass 0 + z 1 • coordinateTorusH1DualClass 1 := by
  apply coordinateTorusH1CohomologyCoordinates.injective
  rw [coordinateTorusH1_linearCombination_coordinates]
  change coordinateTorusH1CohomologyCoordinates
    (coordinateTorusH1CohomologyCoordinates.symm (oneFixedSection z)) = _
  rw [LinearEquiv.apply_symm_apply, oneFixedSection_apply]

/-- The primitive degree-two generator is exactly the difference of the two native dual classes. -/
theorem coordinateTorusH2FixedSection_apply (z : Fin 4 → ℤ) :
    coordinateTorusH2FixedSection z =
      z 0 • coordinateTorusH2DualClass 0 +
        z 1 • (coordinateTorusH2DualClass 1 - coordinateTorusH2DualClass 4) +
        z 2 • coordinateTorusH2DualClass 2 + z 3 • coordinateTorusH2DualClass 3 := by
  apply coordinateTorusH2CohomologyCoordinates.injective
  rw [coordinateTorusH2_linearCombination_coordinates]
  change coordinateTorusH2CohomologyCoordinates
    (coordinateTorusH2CohomologyCoordinates.symm (twoFixedSection z)) = _
  rw [LinearEquiv.apply_symm_apply, twoFixedSection_apply]

/-- The native degree-three section in its original two fixed dual-minor classes. -/
theorem coordinateTorusH3FixedSection_apply (z : Fin 2 → ℤ) :
    coordinateTorusH3FixedSection z =
      z 0 • coordinateTorusH3DualClass 0 + z 1 • coordinateTorusH3DualClass 1 := by
  apply coordinateTorusH3CohomologyCoordinates.injective
  rw [coordinateTorusH3_linearCombination_coordinates]
  change coordinateTorusH3CohomologyCoordinates
    (coordinateTorusH3CohomologyCoordinates.symm (threeFixedSection z)) = _
  rw [LinearEquiv.apply_symm_apply, threeFixedSection_apply]

/-- Actual fixed first-cohomology classes are precisely the integer span of `γ` and `u`. -/
theorem coordinateTorusH1_pullback_fixed_iff_generated
    (x : SingularCohomology (ProductTorus 4) 1) :
    singularCohomologyPullback (torusMatrixMap M₀) 1 x = x ↔
      ∃ a b : ℤ, x =
        a • coordinateTorusH1DualClass 0 + b • coordinateTorusH1DualClass 1 := by
  rw [coordinateTorusH1_pullback_fixed_iff_exists]
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a, b, coordinateTorusH1CohomologyCoordinates.injective ?_⟩
    rw [h, coordinateTorusH1_linearCombination_coordinates]
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, coordinateTorusH1_linearCombination_coordinates a b⟩

/-- Actual fixed second-cohomology classes are precisely the integer span of
`γu`, `γw-uδ`, `γδ`, and `uw`, with these labels denoting dual-minor classes. -/
theorem coordinateTorusH2_pullback_fixed_iff_generated
    (x : SingularCohomology (ProductTorus 4) 2) :
    singularCohomologyPullback (torusMatrixMap M₀) 2 x = x ↔
      ∃ a b c d : ℤ, x =
        a • coordinateTorusH2DualClass 0 +
          b • (coordinateTorusH2DualClass 1 - coordinateTorusH2DualClass 4) +
          c • coordinateTorusH2DualClass 2 + d • coordinateTorusH2DualClass 3 := by
  rw [coordinateTorusH2_pullback_fixed_iff_exists]
  constructor
  · rintro ⟨a, b, c, d, h⟩
    refine ⟨a, b, c, d, coordinateTorusH2CohomologyCoordinates.injective ?_⟩
    rw [h, coordinateTorusH2_linearCombination_coordinates]
  · rintro ⟨a, b, c, d, rfl⟩
    exact ⟨a, b, c, d, coordinateTorusH2_linearCombination_coordinates a b c d⟩

/-- Actual fixed third-cohomology classes are precisely the integer span of the
two native dual-minor classes labelled `γuw` and `γuδ`. -/
theorem coordinateTorusH3_pullback_fixed_iff_generated
    (x : SingularCohomology (ProductTorus 4) 3) :
    singularCohomologyPullback (torusMatrixMap M₀) 3 x = x ↔
      ∃ a b : ℤ, x =
        a • coordinateTorusH3DualClass 0 + b • coordinateTorusH3DualClass 1 := by
  rw [coordinateTorusH3_pullback_fixed_iff_exists]
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a, b, coordinateTorusH3CohomologyCoordinates.injective ?_⟩
    rw [h, coordinateTorusH3_linearCombination_coordinates]
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, coordinateTorusH3_linearCombination_coordinates a b⟩

end Wikipedia.HopfProblem.CuspCentralCohomology
