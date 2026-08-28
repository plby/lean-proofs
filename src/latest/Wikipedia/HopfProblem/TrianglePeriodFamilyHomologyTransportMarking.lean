import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportTorus
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportMarking

/-!
# Canonical higher homology of the literal descended fibres

The actual flat-fibre homeomorphism transports the positive ordered exterior
marking to the actual singular homology of the literal family fibre.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior

variable {V B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
  (D : TrianglePeriodFamily.Data V B)
  (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

include hq

/-- The canonical exterior marking of actual degree-2 homology of the literal fibre. -/
def fibreSingularH2Equiv (b : B) :
    SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2 ≃ₗ[ℤ] latticeExterior 2 :=
  (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) 2).symm.trans
    FlatTorus.singularH2Equiv

theorem fibreSingularH2Equiv_inducedHomology_flat (b : B)
    (a : SingularHomology RealTorus₄ 2) :
    D.fibreSingularH2Equiv hq b
      (singularHomologyMap (D.flatFibreHomeomorph hq b :
        C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 2 a) =
      FlatTorus.singularH2Equiv a := by
  change FlatTorus.singularH2Equiv
    ((homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) 2).symm
      (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) 2 a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The actual fibre homology in the source's ordered minor coordinates. -/
def fibreSingularH2Coordinates (b : B) :
    SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  (D.fibreSingularH2Equiv hq b).trans squareCoordinates

theorem fibreSingularH2_free (b : B) :
    Module.Free ℤ (SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2) :=
  Module.Free.of_equiv (D.fibreSingularH2Equiv hq b).symm

theorem fibreSingularH2_finite (b : B) :
    Module.Finite ℤ (SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2) :=
  Module.Finite.of_surjective (D.fibreSingularH2Equiv hq b).symm.toLinearMap
    (D.fibreSingularH2Equiv hq b).symm.surjective

theorem fibreSingularH2_finrank (b : B) :
    Module.finrank ℤ (SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2) = 6 := by
  rw [(D.fibreSingularH2Equiv hq b).finrank_eq, latticeExterior_finrank]
  decide

/-- The canonical exterior marking of actual degree-3 homology of the literal fibre. -/
def fibreSingularH3Equiv (b : B) :
    SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3 ≃ₗ[ℤ] latticeExterior 3 :=
  (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) 3).symm.trans
    FlatTorus.singularH3Equiv

theorem fibreSingularH3Equiv_inducedHomology_flat (b : B)
    (a : SingularHomology RealTorus₄ 3) :
    D.fibreSingularH3Equiv hq b
      (singularHomologyMap (D.flatFibreHomeomorph hq b :
        C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 3 a) =
      FlatTorus.singularH3Equiv a := by
  change FlatTorus.singularH3Equiv
    ((homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) 3).symm
      (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) 3 a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The actual fibre homology in the source's ordered minor coordinates. -/
def fibreSingularH3Coordinates (b : B) :
    SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (D.fibreSingularH3Equiv hq b).trans cubeCoordinates

theorem fibreSingularH3_free (b : B) :
    Module.Free ℤ (SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3) :=
  Module.Free.of_equiv (D.fibreSingularH3Equiv hq b).symm

theorem fibreSingularH3_finite (b : B) :
    Module.Finite ℤ (SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3) :=
  Module.Finite.of_surjective (D.fibreSingularH3Equiv hq b).symm.toLinearMap
    (D.fibreSingularH3Equiv hq b).symm.surjective

theorem fibreSingularH3_finrank (b : B) :
    Module.finrank ℤ (SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3) = 4 := by
  rw [(D.fibreSingularH3Equiv hq b).finrank_eq, latticeExterior_finrank]
  decide

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
