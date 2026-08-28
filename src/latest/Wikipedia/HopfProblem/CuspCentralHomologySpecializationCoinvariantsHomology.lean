import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsCoordinates
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsTransport
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarkingProductTorus
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual torus homology coinvariants of the single cusp action

The canonical positive-loop exterior markings intertwine the actual singular
homology maps of `torusMatrixMap M₀` with the actual ordered exterior-minor
matrices. They therefore transport the explicit integral matrix coinvariants
to actual second and third singular homology. This proves their ranks and
gives representatives, without asserting any geometric specialization result.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants

open SingularMayerVietoris PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior

/-- The actual degree-`q` homology action of the cusp torus map minus identity. -/
def torusDifference (q : ℕ) :
    SingularHomology (ProductTorus 4) q →ₗ[ℤ] SingularHomology (ProductTorus 4) q :=
  singularHomologyMap (torusMatrixMap M₀) q - LinearMap.id

@[simp] theorem torusDifference_apply (q : ℕ) (a : SingularHomology (ProductTorus 4) q) :
    torusDifference q a = singularHomologyMap (torusMatrixMap M₀) q a - a := rfl

/-- Canonical second-homology coordinates intertwine the actual difference maps. -/
theorem torusDifference_two_coordinates (a : SingularHomology (ProductTorus 4) 2) :
    coordinateTorusH2Coordinates (torusDifference 2 a) =
      squareDifference (coordinateTorusH2Coordinates a) := by
  rw [torusDifference_apply, map_sub, coordinateTorusH2Coordinates_matrix]
  simp only [squareDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec, squareM₀]

/-- Canonical third-homology coordinates intertwine the actual difference maps. -/
theorem torusDifference_three_coordinates (a : SingularHomology (ProductTorus 4) 3) :
    coordinateTorusH3Coordinates (torusDifference 3 a) =
      cubeDifference (coordinateTorusH3Coordinates a) := by
  rw [torusDifference_apply, map_sub, coordinateTorusH3Coordinates_matrix]
  simp only [cubeDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec, cubeM₀]

/-- The literal quotient of actual torus homology by its single cusp-action relations. -/
abbrev TorusCoinvariants (q : ℕ) :=
  SingularHomology (ProductTorus 4) q ⧸ LinearMap.range (torusDifference q)

/-- Four free integral coordinates on the actual degree-two torus coinvariants. -/
def torusTwoCoinvariantEquiv : TorusCoinvariants 2 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ((quotientRangeEquiv coordinateTorusH2Coordinates (torusDifference 2) squareDifference
    torusDifference_two_coordinates).toAddEquiv.trans
      squareCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

/-- Two free integral coordinates on the actual degree-three torus coinvariants. -/
def torusThreeCoinvariantEquiv : TorusCoinvariants 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((quotientRangeEquiv coordinateTorusH3Coordinates (torusDifference 3) cubeDifference
    torusDifference_three_coordinates).toAddEquiv.trans
      cubeCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

@[simp] theorem torusTwoCoinvariantEquiv_mk (a : SingularHomology (ProductTorus 4) 2) :
    torusTwoCoinvariantEquiv (Submodule.Quotient.mk a) =
      squareProjection (coordinateTorusH2Coordinates a) := by
  change squareCoinvariantEquiv
    (quotientRangeEquiv coordinateTorusH2Coordinates (torusDifference 2) squareDifference
      torusDifference_two_coordinates (Submodule.Quotient.mk a)) = _
  rw [quotientRangeEquiv_mk, squareCoinvariantEquiv_mk]
  rfl

@[simp] theorem torusThreeCoinvariantEquiv_mk (a : SingularHomology (ProductTorus 4) 3) :
    torusThreeCoinvariantEquiv (Submodule.Quotient.mk a) =
      cubeProjection (coordinateTorusH3Coordinates a) := by
  change cubeCoinvariantEquiv
    (quotientRangeEquiv coordinateTorusH3Coordinates (torusDifference 3) cubeDifference
      torusDifference_three_coordinates (Submodule.Quotient.mk a)) = _
  rw [quotientRangeEquiv_mk, cubeCoinvariantEquiv_mk]
  rfl

theorem torusTwoCoinvariantEquiv_mk_coordinates
    (a : SingularHomology (ProductTorus 4) 2) :
    torusTwoCoinvariantEquiv (Submodule.Quotient.mk a) =
      ![coordinateTorusH2Coordinates a 0, coordinateTorusH2Coordinates a 2,
        coordinateTorusH2Coordinates a 3,
        coordinateTorusH2Coordinates a 4 - coordinateTorusH2Coordinates a 1] :=
  torusTwoCoinvariantEquiv_mk a

theorem torusThreeCoinvariantEquiv_mk_coordinates
    (a : SingularHomology (ProductTorus 4) 3) :
    torusThreeCoinvariantEquiv (Submodule.Quotient.mk a) =
      ![coordinateTorusH3Coordinates a 0, coordinateTorusH3Coordinates a 1] :=
  torusThreeCoinvariantEquiv_mk a

/-- Representatives are the actual homology classes with the explicit section coordinates. -/
@[simp] theorem torusTwoCoinvariantEquiv_symm_apply (z : Fin 4 → ℤ) :
    torusTwoCoinvariantEquiv.symm z =
      Submodule.Quotient.mk (coordinateTorusH2Coordinates.symm (squareSection z)) := by
  apply torusTwoCoinvariantEquiv.injective
  rw [LinearEquiv.apply_symm_apply, torusTwoCoinvariantEquiv_mk,
    LinearEquiv.apply_symm_apply, squareProjection_section]

@[simp] theorem torusThreeCoinvariantEquiv_symm_apply (z : Fin 2 → ℤ) :
    torusThreeCoinvariantEquiv.symm z =
      Submodule.Quotient.mk (coordinateTorusH3Coordinates.symm (cubeSection z)) := by
  apply torusThreeCoinvariantEquiv.injective
  rw [LinearEquiv.apply_symm_apply, torusThreeCoinvariantEquiv_mk,
    LinearEquiv.apply_symm_apply, cubeProjection_section]

theorem torusTwoCoinvariant_finrank : Module.finrank ℤ (TorusCoinvariants 2) = 4 := by
  rw [torusTwoCoinvariantEquiv.finrank_eq, Module.finrank_fin_fun]

theorem torusThreeCoinvariant_finrank : Module.finrank ℤ (TorusCoinvariants 3) = 2 := by
  rw [torusThreeCoinvariantEquiv.finrank_eq, Module.finrank_fin_fun]

theorem torusTwoCoinvariant_free : Module.Free ℤ (TorusCoinvariants 2) :=
  Module.Free.of_equiv torusTwoCoinvariantEquiv.symm

theorem torusThreeCoinvariant_free : Module.Free ℤ (TorusCoinvariants 3) :=
  Module.Free.of_equiv torusThreeCoinvariantEquiv.symm

theorem torusTwoCoinvariant_finite : Module.Finite ℤ (TorusCoinvariants 2) :=
  Module.Finite.of_surjective torusTwoCoinvariantEquiv.symm.toLinearMap
    torusTwoCoinvariantEquiv.symm.surjective

theorem torusThreeCoinvariant_finite : Module.Finite ℤ (TorusCoinvariants 3) :=
  Module.Finite.of_surjective torusThreeCoinvariantEquiv.symm.toLinearMap
    torusThreeCoinvariantEquiv.symm.surjective

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants
