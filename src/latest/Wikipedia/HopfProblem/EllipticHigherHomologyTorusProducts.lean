import Wikipedia.HopfProblem.EllipticHigherHomologyTorusH1
import Wikipedia.HopfProblem.EllipticHigherHomologyTorusWedge

/-!
# Actual exterior products of the elliptic three-torus coordinate loops

These exterior-square and exterior-cube maps are defined using the actual
positive vector-loop marking. Their surjectivity follows from the proved
coordinate-subtorus homology basis, and their matrix naturality follows
from naturality of actual singular-chain Pontryagin products.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyPontryagin

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

/-- The actual exterior-square product of positive rank-three coordinate loops. -/
def torusWedgeTwo :
    (⋀[ℤ]^2 FibreLattice) →ₗ[ℤ] SingularHomology (ProductTorus 3) 2 := by
  letI := productTorus_homology_torsionFree 3 2
  exact markedWedgeTwo (ProductTorus 3) (coordinateH1 3)

/-- The actual exterior-cube product of positive rank-three coordinate loops. -/
def torusWedgeThree :
    (⋀[ℤ]^3 FibreLattice) →ₗ[ℤ] SingularHomology (ProductTorus 3) 3 := by
  letI := productTorus_homology_torsionFree 3 2
  exact markedWedgeThree (ProductTorus 3) (coordinateH1 3)

@[simp] theorem torusWedgeTwo_ιMulti (v : Fin 2 → FibreLattice) :
    torusWedgeTwo (exteriorPower.ιMulti ℤ 2 v) =
      product11 (ProductTorus 3) (coordinateH1 3 (v 0)) (coordinateH1 3 (v 1)) := by
  let := productTorus_homology_torsionFree 3 2
  exact markedWedgeTwo_apply_ιMulti (ProductTorus 3) (coordinateH1 3) v

@[simp] theorem torusWedgeThree_ιMulti (v : Fin 3 → FibreLattice) :
    torusWedgeThree (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct (ProductTorus 3) (coordinateH1 3 (v 0))
        (coordinateH1 3 (v 1)) (coordinateH1 3 (v 2)) := by
  let := productTorus_homology_torsionFree 3 2
  exact markedWedgeThree_apply_ιMulti (ProductTorus 3) (coordinateH1 3) v

/-- Decomposable exterior squares are represented by the actual ordered vector loops. -/
theorem torusWedgeTwo_ιMulti_loops (v : Fin 2 → FibreLattice) :
    torusWedgeTwo (exteriorPower.ιMulti ℤ 2 v) =
      product11 (ProductTorus 3)
        (loopHomologyClass (coordinatePeriodLoop 3 (v 0)))
        (loopHomologyClass (coordinatePeriodLoop 3 (v 1))) := by
  rw [torusWedgeTwo_ιMulti, coordinateH1_three_apply, coordinateH1_three_apply]

/-- Decomposable exterior cubes are represented by the actual ordered vector loops. -/
theorem torusWedgeThree_ιMulti_loops (v : Fin 3 → FibreLattice) :
    torusWedgeThree (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct (ProductTorus 3)
        (loopHomologyClass (coordinatePeriodLoop 3 (v 0)))
        (loopHomologyClass (coordinatePeriodLoop 3 (v 1)))
        (loopHomologyClass (coordinatePeriodLoop 3 (v 2))) := by
  rw [torusWedgeThree_ιMulti, coordinateH1_three_apply, coordinateH1_three_apply,
    coordinateH1_three_apply]

/-- An additive continuous map respects the square products of any compatible marking. -/
theorem torusWedgeTwo_natural (f : C(ProductTorus 3, ProductTorus 3))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : FibreLattice →ₗ[ℤ] FibreLattice)
    (hmark : ∀ v, singularHomologyMap f 1 (coordinateH1 3 v) = coordinateH1 3 (A v)) :
    (singularHomologyMap f 2).comp torusWedgeTwo =
      torusWedgeTwo.comp (exteriorPower.map 2 A) := by
  let := productTorus_homology_torsionFree 3 2
  exact markedWedgeTwo_natural f hf (coordinateH1 3) (coordinateH1 3) A hmark

/-- An additive continuous map respects the cube products of any compatible marking. -/
theorem torusWedgeThree_natural (f : C(ProductTorus 3, ProductTorus 3))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : FibreLattice →ₗ[ℤ] FibreLattice)
    (hmark : ∀ v, singularHomologyMap f 1 (coordinateH1 3 v) = coordinateH1 3 (A v)) :
    (singularHomologyMap f 3).comp torusWedgeThree =
      torusWedgeThree.comp (exteriorPower.map 3 A) := by
  let := productTorus_homology_torsionFree 3 2
  exact markedWedgeThree_natural f hf (coordinateH1 3) (coordinateH1 3) A hmark

/-- Every integral three-by-three matrix acts by its actual exterior-square map. -/
theorem torusWedgeTwo_matrix (A : FibreMatrix) :
    (singularHomologyMap (torusMatrixMap A) 2).comp torusWedgeTwo =
      torusWedgeTwo.comp (exteriorPower.map 2 A.mulVecLin) :=
  torusWedgeTwo_natural (torusMatrixMap A) (torusMatrixMap_add A) A.mulVecLin
    (coordinateH1_three_matrix_natural A)

/-- Every integral three-by-three matrix acts by its actual exterior-cube map. -/
theorem torusWedgeThree_matrix (A : FibreMatrix) :
    (singularHomologyMap (torusMatrixMap A) 3).comp torusWedgeThree =
      torusWedgeThree.comp (exteriorPower.map 3 A.mulVecLin) :=
  torusWedgeThree_natural (torusMatrixMap A) (torusMatrixMap_add A) A.mulVecLin
    (coordinateH1_three_matrix_natural A)

/-- Actual products of the marked loops generate all second singular homology. -/
theorem torusWedgeTwo_surjective : Function.Surjective torusWedgeTwo := by
  let := productTorus_homology_torsionFree 3 2
  exact markedWedgeTwo_surjective_of_torusHomeomorph
    (Homeomorph.refl (ProductTorus 3)) (fun _ _ => rfl)
    (coordinateH1 3) coordinateH1_three_bijective.surjective

/-- Actual products of the marked loops generate all third singular homology. -/
theorem torusWedgeThree_surjective : Function.Surjective torusWedgeThree := by
  let := productTorus_homology_torsionFree 3 2
  exact markedWedgeThree_surjective_of_torusHomeomorph
    (Homeomorph.refl (ProductTorus 3)) (fun _ _ => rfl)
    (coordinateH1 3) coordinateH1_three_bijective.surjective

end Wikipedia.HopfProblem.Elliptic.HigherHomology
