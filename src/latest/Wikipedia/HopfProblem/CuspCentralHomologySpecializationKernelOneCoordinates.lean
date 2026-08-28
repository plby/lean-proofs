import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusDegreeOne
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjectiveProductTorus

/-!
# The fixed positive-loop marking and its integral degree-one coinvariants

The marking is the inverse of the existing map of positive coordinate
loop classes, in their original order.  The auxiliary period matrix only
certifies that this fixed map is bijective.  The actual torus matrix map
acts by its literal integer matrix in these coordinates.  Its difference
from identity therefore has exactly the previously computed integral
coinvariants, without choosing a specialization-dependent marking.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open SpecializationCoinvariants

/-- The one fixed degree-one marking, inverse to actual positive coordinate-loop classes. -/
def coordinateTorusH1Coordinates :
    SingularHomology (ProductTorus 4) 1 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (coordinateH1FourEquiv (Elliptic.examplePeriod .four)).symm

@[simp] theorem coordinateTorusH1Coordinates_symm_apply (v : Fin 4 → ℤ) :
    coordinateTorusH1Coordinates.symm v = coordinateH1 4 v := rfl

@[simp] theorem coordinateTorusH1Coordinates_coordinateH1 (v : Fin 4 → ℤ) :
    coordinateTorusH1Coordinates (coordinateH1 4 v) = v :=
  (coordinateH1FourEquiv (Elliptic.examplePeriod .four)).symm_apply_apply v

/-- Every actual straight vector loop has precisely its original integer coordinates. -/
@[simp] theorem coordinateTorusH1Coordinates_loop (v : Fin 4 → ℤ) :
    coordinateTorusH1Coordinates (loopHomologyClass (coordinatePeriodLoop 4 v)) = v := by
  rw [← coordinateH1_four_apply (Elliptic.examplePeriod .four),
    coordinateTorusH1Coordinates_coordinateH1]

/-- The actual matrix map has the literal matrix in the fixed positive-loop marking. -/
theorem coordinateTorusH1Coordinates_matrix (A : LatticeMatrix)
    (a : SingularHomology (ProductTorus 4) 1) :
    coordinateTorusH1Coordinates (singularHomologyMap (torusMatrixMap A) 1 a) =
      A *ᵥ coordinateTorusH1Coordinates a := by
  obtain ⟨v, hv⟩ := (coordinateH1FourEquiv (Elliptic.examplePeriod .four)).surjective a
  change coordinateH1 4 v = a at hv
  rw [← hv, singularHomologyMap_one,
    coordinateH1_matrix_natural (Elliptic.examplePeriod .four),
    coordinateTorusH1Coordinates_coordinateH1, coordinateTorusH1Coordinates_coordinateH1]

/-- The actual degree-one difference intertwines the fixed integral coordinate difference. -/
theorem torusDifference_one_coordinates (a : SingularHomology (ProductTorus 4) 1) :
    coordinateTorusH1Coordinates (torusDifference 1 a) =
      oneDifference (coordinateTorusH1Coordinates a) := by
  rw [torusDifference_apply, map_sub, coordinateTorusH1Coordinates_matrix]
  simp only [oneDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]

/-- The literal degree-one torus coinvariant quotient has two free integral coordinates. -/
def torusOneCoinvariantEquiv : TorusCoinvariants 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((quotientRangeEquiv coordinateTorusH1Coordinates (torusDifference 1) oneDifference
    torusDifference_one_coordinates).toAddEquiv.trans
      oneCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

@[simp] theorem torusOneCoinvariantEquiv_mk (a : SingularHomology (ProductTorus 4) 1) :
    torusOneCoinvariantEquiv (Submodule.Quotient.mk a) =
      oneProjection (coordinateTorusH1Coordinates a) := by
  change oneCoinvariantEquiv
    (quotientRangeEquiv coordinateTorusH1Coordinates (torusDifference 1) oneDifference
      torusDifference_one_coordinates (Submodule.Quotient.mk a)) = _
  rw [quotientRangeEquiv_mk, oneCoinvariantEquiv_mk]
  rfl

@[simp] theorem torusOneCoinvariantEquiv_symm_apply (z : Fin 2 → ℤ) :
    torusOneCoinvariantEquiv.symm z =
      Submodule.Quotient.mk (coordinateTorusH1Coordinates.symm (oneSection z)) := by
  apply torusOneCoinvariantEquiv.injective
  rw [LinearEquiv.apply_symm_apply, torusOneCoinvariantEquiv_mk,
    LinearEquiv.apply_symm_apply, oneProjection_section]

theorem torusOneCoinvariant_finrank : Module.finrank ℤ (TorusCoinvariants 1) = 2 := by
  rw [torusOneCoinvariantEquiv.finrank_eq, Module.finrank_fin_fun]

theorem torusOneCoinvariant_free : Module.Free ℤ (TorusCoinvariants 1) :=
  Module.Free.of_equiv torusOneCoinvariantEquiv.symm

theorem torusOneCoinvariant_finite : Module.Finite ℤ (TorusCoinvariants 1) :=
  Module.Finite.of_surjective torusOneCoinvariantEquiv.symm.toLinearMap
    torusOneCoinvariantEquiv.symm.surjective

/-- Range membership is exact over the integers in the original four coordinates. -/
theorem torusDifference_one_mem_range_iff (a : SingularHomology (ProductTorus 4) 1) :
    a ∈ LinearMap.range (torusDifference 1) ↔
      ∃ v : Fin 4 → ℤ, (M₀ - 1) *ᵥ v = coordinateTorusH1Coordinates a := by
  exact mem_range_iff_of_intertwines coordinateTorusH1Coordinates
    (torusDifference 1) oneDifference torusDifference_one_coordinates a

/-- The two surviving coordinates vanish precisely on the actual monodromy image. -/
theorem torusDifference_one_range_iff (a : SingularHomology (ProductTorus 4) 1) :
    a ∈ LinearMap.range (torusDifference 1) ↔
      coordinateTorusH1Coordinates a 0 = 0 ∧ coordinateTorusH1Coordinates a 1 = 0 :=
  (mem_range_iff_of_intertwines coordinateTorusH1Coordinates
    (torusDifference 1) oneDifference torusDifference_one_coordinates a).trans
      (oneDifference_range_iff (coordinateTorusH1Coordinates a))

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
