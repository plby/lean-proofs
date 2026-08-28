import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeFullPeriod
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeProductTorus

/-!
# Full-period wedge maps in actual product-torus coordinates

The original integral order `(m₀,m₁,n₀,n₁)` is retained. The proved full-period
coordinate homeomorphism carries the actual marked exterior maps to the actual
positive coordinate-loop exterior maps of the product torus.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomologyPontryagin

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual coordinate-loop marking agrees with the full-period marking. -/
theorem coordinateH1_four_eq_fullPeriodMarking (q : FullPeriodMatrix) :
    coordinateH1 4 =
      (singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 1).comp
        (fullPeriodCoordinateH1 q) := by
  apply (Pi.basisFun ℤ (Fin 4)).ext
  intro i
  change coordinateH1 4 (Pi.basisFun ℤ (Fin 4) i) =
    singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 1
      (fullPeriodCoordinateH1 q (Pi.basisFun ℤ (Fin 4) i))
  rw [coordinateH1_basis, fullPeriodCoordinateH1_productTorusHomeomorph]
  simp only [Pi.basisFun_apply]

theorem fullPeriodCoordinateH1_coordinates (q : FullPeriodMatrix) (v : Lattice) :
    singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 1
        (fullPeriodCoordinateH1 q v) = coordinateH1 4 v :=
  (LinearMap.congr_fun (coordinateH1_four_eq_fullPeriodMarking q) v).symm

/-- The actual full-period coordinate homeomorphism preserves the degree-two exterior map. -/
theorem fullPeriodTorusWedgeTwo_coordinates (q : FullPeriodMatrix) :
    (singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 2).comp
        (fullPeriodTorusWedgeTwo q) = coordinateTorusWedgeTwo := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 2
      (fullPeriodTorusWedgeTwo q (exteriorPower.ιMulti ℤ 2 v)) =
    coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v)
  rw [fullPeriodTorusWedgeTwo_apply_ιMulti, coordinateTorusWedgeTwo_apply_ιMulti,
    product_natural _ q.productTorusHomeomorph_add 1,
    fullPeriodCoordinateH1_coordinates, fullPeriodCoordinateH1_coordinates]

/-- The same actual homeomorphism preserves the degree-three exterior map. -/
theorem fullPeriodTorusWedgeThree_coordinates (q : FullPeriodMatrix) :
    (singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 3).comp
        (fullPeriodTorusWedgeThree q) = coordinateTorusWedgeThree := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 3
      (fullPeriodTorusWedgeThree q (exteriorPower.ιMulti ℤ 3 v)) =
    coordinateTorusWedgeThree (exteriorPower.ιMulti ℤ 3 v)
  rw [fullPeriodTorusWedgeThree_apply_ιMulti, coordinateTorusWedgeThree_apply_ιMulti,
    tripleProduct_natural _ q.productTorusHomeomorph_add,
    fullPeriodCoordinateH1_coordinates, fullPeriodCoordinateH1_coordinates,
    fullPeriodCoordinateH1_coordinates]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
