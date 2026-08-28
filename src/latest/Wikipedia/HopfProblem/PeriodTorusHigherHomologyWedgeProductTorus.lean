import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgePeriodThree
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusDegreeOne

/-!
# The actual coordinate-loop exterior maps of the product torus

The exterior maps use the literal positive coordinate-loop marking of first
homology. Naturality under actual integer-matrix maps and under the actual
period-to-circle homeomorphisms follows from the constructed Pontryagin products.
No bijectivity of the exterior maps is asserted here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomologyPontryagin

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual degree-two exterior map in the positive coordinate-loop marking. -/
def coordinateTorusWedgeTwo :
    (⋀[ℤ]^2 Lattice) →ₗ[ℤ] SingularHomology (ProductTorus 4) 2 := by
  letI := productTorus_homology_torsionFree 4 2
  exact latticeWedgeTwo (ProductTorus 4) (coordinateH1 4)

/-- The actual degree-three exterior map in the positive coordinate-loop marking. -/
def coordinateTorusWedgeThree :
    (⋀[ℤ]^3 Lattice) →ₗ[ℤ] SingularHomology (ProductTorus 4) 3 := by
  letI := productTorus_homology_torsionFree 4 2
  exact latticeWedgeThree (ProductTorus 4) (coordinateH1 4)

@[simp] theorem coordinateTorusWedgeTwo_apply_ιMulti (v : Fin 2 → Lattice) :
    coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v) =
      product11 (ProductTorus 4) (coordinateH1 4 (v 0)) (coordinateH1 4 (v 1)) := by
  let := productTorus_homology_torsionFree 4 2
  exact latticeWedgeTwo_apply_ιMulti (ProductTorus 4) (coordinateH1 4) v

@[simp] theorem coordinateTorusWedgeThree_apply_ιMulti (v : Fin 3 → Lattice) :
    coordinateTorusWedgeThree (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct (ProductTorus 4) (coordinateH1 4 (v 0))
        (coordinateH1 4 (v 1)) (coordinateH1 4 (v 2)) := by
  let := productTorus_homology_torsionFree 4 2
  exact latticeWedgeThree_apply_ιMulti (ProductTorus 4) (coordinateH1 4) v

theorem coordinateTorusWedgeTwo_apply_ιMulti_periodLoops
    (p : PeriodDomain) (v : Fin 2 → Lattice) :
    coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v) =
      product11 (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (v 0)))
        (loopHomologyClass (coordinatePeriodLoop 4 (v 1))) := by
  rw [coordinateTorusWedgeTwo_apply_ιMulti, coordinateH1_four_apply p,
    coordinateH1_four_apply p]

theorem coordinateTorusWedgeThree_apply_ιMulti_periodLoops
    (p : PeriodDomain) (v : Fin 3 → Lattice) :
    coordinateTorusWedgeThree (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (v 0)))
        (loopHomologyClass (coordinatePeriodLoop 4 (v 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (v 2))) := by
  rw [coordinateTorusWedgeThree_apply_ιMulti, coordinateH1_four_apply p,
    coordinateH1_four_apply p, coordinateH1_four_apply p]

/-- Actual integer-matrix maps act naturally on the actual coordinate exterior square. -/
theorem coordinateTorusWedgeTwo_matrix (p : PeriodDomain) (A : LatticeMatrix) :
    (singularHomologyMap (torusMatrixMap A) 2).comp coordinateTorusWedgeTwo =
      coordinateTorusWedgeTwo.comp (exteriorPower.map 2 A.mulVecLin) := by
  let := productTorus_homology_torsionFree 4 2
  exact latticeWedgeTwo_natural (torusMatrixMap A)
    (fun x y => (torusMatrixLinearMap A).map_add x y)
    (coordinateH1 4) (coordinateH1 4) A.mulVecLin (coordinateH1_matrix_natural p A)

/-- Actual integer-matrix maps act naturally on the actual coordinate exterior cube. -/
theorem coordinateTorusWedgeThree_matrix (p : PeriodDomain) (A : LatticeMatrix) :
    (singularHomologyMap (torusMatrixMap A) 3).comp coordinateTorusWedgeThree =
      coordinateTorusWedgeThree.comp (exteriorPower.map 3 A.mulVecLin) := by
  let := productTorus_homology_torsionFree 4 2
  exact latticeWedgeThree_natural (torusMatrixMap A)
    (fun x y => (torusMatrixLinearMap A).map_add x y)
    (coordinateH1 4) (coordinateH1 4) A.mulVecLin (coordinateH1_matrix_natural p A)

/-- The actual period-coordinate homeomorphism preserves the canonical exterior-square map. -/
theorem periodTorusWedgeTwo_coordinates (p : PeriodDomain) :
    (singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 2).comp
        (periodTorusWedgeTwo p) = coordinateTorusWedgeTwo := by
  have hmark (v : Lattice) :
      singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 1
          (p.singularH1Equiv.symm v) = coordinateH1 4 v :=
    (LinearMap.congr_fun (coordinateH1_four_eq_periodMarking p) v).symm
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 2
      (periodTorusWedgeTwo p (exteriorPower.ιMulti ℤ 2 v)) =
    coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v)
  rw [periodTorusWedgeTwo_apply_ιMulti, coordinateTorusWedgeTwo_apply_ιMulti,
    product_natural _ (periodTorusCircleHomeomorph_add p) 1, hmark, hmark]

/-- The actual period-coordinate homeomorphism preserves the canonical exterior-cube map. -/
theorem periodTorusWedgeThree_coordinates (p : PeriodDomain) :
    (singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 3).comp
        (periodTorusWedgeThree p) = coordinateTorusWedgeThree := by
  have hmark (v : Lattice) :
      singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 1
          (p.singularH1Equiv.symm v) = coordinateH1 4 v :=
    (LinearMap.congr_fun (coordinateH1_four_eq_periodMarking p) v).symm
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 3
      (periodTorusWedgeThree p (exteriorPower.ιMulti ℤ 3 v)) =
    coordinateTorusWedgeThree (exteriorPower.ιMulti ℤ 3 v)
  rw [periodTorusWedgeThree_apply_ιMulti, coordinateTorusWedgeThree_apply_ιMulti,
    tripleProduct_natural _ (periodTorusCircleHomeomorph_add p), hmark, hmark, hmark]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
