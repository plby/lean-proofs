import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationShear
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitTwo
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepFlatProduct

/-!
# The genuine fibre corrections are four and minus three

The original elliptic split classes are actual ordered Pontryagin
products in the original flat torus. Repeated first factors give zero,
and the full native third-homology marking fixes the positive `gamma,u,w`
class. Applying the actual vertical-shear formula to the two covering
representatives therefore yields coefficients four and minus three.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open Elliptic Elliptic.HigherHomology FirstHurewicz SingularMayerVietoris
open PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior
open PeriodTorusHigherHomologyPontryagin LocalSystemMatrices EllipticCapKernelWang
open SpecialPeriods.Threefold.Homology.DeltaSweep

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

/-- The original ordered triple product is its genuine exterior-cube class. -/
theorem flat_tripleProduct_exterior (a b c : Lattice) :
    FlatTorus.singularH3Equiv
      (tripleProduct RealTorus₄ (FlatTorus.singularH1Equiv.symm a)
        (FlatTorus.singularH1Equiv.symm b) (FlatTorus.singularH1Equiv.symm c)) =
      exteriorPower.ιMulti ℤ 3 ![a, b, c] := by
  rw [FlatTorus.singularH3Equiv_apply,
    tripleProduct_natural _ flatTorusCircleHomeomorph_add,
    FlatTorus.coordinateH1_flatMarking, FlatTorus.coordinateH1_flatMarking,
    FlatTorus.coordinateH1_flatMarking]
  calc
    _ = coordinateTorusH3ExteriorEquiv
        (coordinateTorusWedgeThree (exteriorPower.ιMulti ℤ 3 ![a, b, c])) :=
      congrArg coordinateTorusH3ExteriorEquiv
        (coordinateTorusWedgeThree_apply_ιMulti ![a, b, c]).symm
    _ = _ := coordinateTorusH3ExteriorEquiv_wedge _

/-- The actual `a,u,w` triple has precisely its two indicated original coordinates. -/
theorem flat_triple_uw_coordinates (a : Lattice) :
    FlatTorus.singularH3Coordinates
      (tripleProduct RealTorus₄ (FlatTorus.singularH1Equiv.symm a)
        (FlatTorus.singularH1Equiv.symm (Pi.single 1 1))
        (FlatTorus.singularH1Equiv.symm (Pi.single 2 1))) = ![a 0, 0, 0, a 3] := by
  rw [FlatTorus.singularH3Coordinates_apply, flat_tripleProduct_exterior]
  funext i
  rw [cubeCoordinates_apply, cubeBasis, Module.Basis.repr_reindex_apply]
  change ((Pi.basisFun ℤ (Fin 4)).exteriorPower 3).repr
    (exteriorPower.ιMulti ℤ 3 ![a, Pi.single 1 1, Pi.single 2 1]) (tripleSubset i) = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [tripleSubset_ordered, Module.Basis.coord_apply, Pi.basisFun_repr]
  fin_cases i <;> simp [tripleIndices, Matrix.det_fin_three]

/-- The actual positive original first exterior-cube coordinate. -/
def gammaUWClass : SingularHomology RealTorus₄ 3 :=
  FlatTorus.singularH3Coordinates.symm ![1, 0, 0, 0]

@[simp] theorem gammaUWClass_coordinates :
    FlatTorus.singularH3Coordinates gammaUWClass = ![1, 0, 0, 0] :=
  FlatTorus.singularH3Coordinates.apply_symm_apply _

/-- This marking is the actual ordered product of the three positive original periods. -/
theorem gammaUWClass_eq_tripleProduct :
    gammaUWClass = tripleProduct RealTorus₄
      (FlatTorus.singularH1Equiv.symm (Pi.single 0 1))
      (FlatTorus.singularH1Equiv.symm (Pi.single 1 1))
      (FlatTorus.singularH1Equiv.symm (Pi.single 2 1)) := by
  apply FlatTorus.singularH3Coordinates.injective
  rw [gammaUWClass_coordinates, flat_triple_uw_coordinates]
  simp

/-- The unchanged split-fibre class is the genuine positive `u,w` product. -/
theorem splitFibreClassTwo_eq_product (j : Kind) :
    splitFibreClassTwo j = product11 RealTorus₄
      (FlatTorus.singularH1Equiv.symm (Pi.single 1 1))
      (FlatTorus.singularH1Equiv.symm (Pi.single 2 1)) := by
  apply FlatTorus.singularH2Coordinates.injective
  rw [splitFibreClassTwo_coordinates, flat_product11_coordinates]
  simp

/-- The unchanged split-circle class is the actual twist followed by the positive `w` period. -/
theorem splitCircleClassTwo_eq_product (j : Kind) :
    splitCircleClassTwo j = product11 RealTorus₄
      (FlatTorus.singularH1Equiv.symm j.twist)
      (FlatTorus.singularH1Equiv.symm (Pi.single 2 1)) := by
  apply FlatTorus.singularH2Coordinates.injective
  rw [splitCircleClassTwo_coordinates, flat_product11_coordinates]
  cases j <;> simp [Kind.twist, ε, ε']

/-- The complete original fibre product, not only its regular-family source projection. -/
theorem twist_product_splitFibre (j : Kind) :
    product RealTorus₄ 2 (FlatTorus.singularH1Equiv.symm j.twist)
      (splitFibreClassTwo j) = j.twist 0 • gammaUWClass := by
  rw [splitFibreClassTwo_eq_product]
  apply FlatTorus.singularH3Coordinates.injective
  change FlatTorus.singularH3Coordinates
      (tripleProduct RealTorus₄ (FlatTorus.singularH1Equiv.symm j.twist)
        (FlatTorus.singularH1Equiv.symm (Pi.single 1 1))
        (FlatTorus.singularH1Equiv.symm (Pi.single 2 1))) = _
  rw [flat_triple_uw_coordinates, map_zsmul, gammaUWClass_coordinates]
  cases j <;> ext i <;> fin_cases i <;> simp [Kind.twist, ε, ε']

/-- The second correction vanishes by the actual repeated-factor alternating law. -/
theorem twist_product_splitCircle (j : Kind) :
    product RealTorus₄ 2 (FlatTorus.singularH1Equiv.symm j.twist)
      (splitCircleClassTwo j) = 0 := by
  rw [splitCircleClassTwo_eq_product]
  have := realTorus_homology_torsionFree 2
  exact tripleProduct_self01 RealTorus₄ _ _

/-- The order-three covering representative contributes four genuine positive fibre classes. -/
theorem three_shear_correction :
    product RealTorus₄ 2 (FlatTorus.singularH1Equiv.symm Kind.three.twist)
      (4 • splitFibreClassTwo .three + 2 • splitCircleClassTwo .three) =
        (4 : ℤ) • gammaUWClass := by
  rw [map_add, map_nsmul, map_nsmul, twist_product_splitFibre, twist_product_splitCircle]
  simp [Kind.twist, ε, ofNat_zsmul]

/-- The order-four covering representative contributes minus three, with its original twist sign. -/
theorem four_shear_correction :
    product RealTorus₄ 2 (FlatTorus.singularH1Equiv.symm Kind.four.twist)
      (3 • splitFibreClassTwo .four - splitCircleClassTwo .four) =
        (-3 : ℤ) • gammaUWClass := by
  rw [map_sub, map_nsmul, twist_product_splitFibre, twist_product_splitCircle]
  simp [Kind.twist, ε', ofNat_zsmul]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
