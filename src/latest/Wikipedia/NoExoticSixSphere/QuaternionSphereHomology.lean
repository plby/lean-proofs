import Wikipedia.NoExoticSixSphere.QuaternionSphere
import Wikipedia.NoExoticSixSphere.ProductThirdHomologyFactors

/-!
# Squaring unit quaternions doubles actual third singular homology

Under the proved product homology equivalence, the diagonal has coordinates
`(a,a)`. Multiplication restricts to the identity on both factor inclusions,
so its induced map adds those coordinates. This proves the squaring formula
without assuming a degree calculation or a homotopy-group multiplication
comparison.
-/

noncomputable section

namespace NoExoticSixSphere.QuaternionSphere

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open ProductThirdHomology

theorem multiply_leftSection : multiply.comp (leftSection one) = ContinuousMap.id Space := by
  apply ContinuousMap.ext
  intro x
  exact multiply_one_right x

theorem multiply_rightSection : multiply.comp (rightSection one) = ContinuousMap.id Space := by
  apply ContinuousMap.ext
  intro x
  exact multiply_one_left x

theorem diagonal_homology (a : SingularHomology Space 3) :
    equivalence one one (singularHomologyMap diagonal 3 a) = (a, a) := by
  apply Prod.ext
  · rw [equivalence_fst, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    change singularHomologyMap (ContinuousMap.id Space) 3 a = a
    rw [singularHomologyMap_id]
    rfl
  · rw [equivalence_snd, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    change singularHomologyMap (ContinuousMap.id Space) 3 a = a
    rw [singularHomologyMap_id]
    rfl

theorem multiply_homology (a b : SingularHomology Space 3) :
    singularHomologyMap multiply 3 ((equivalence one one).symm (a, b)) = a + b := by
  rw [map_product_class, multiply_leftSection, multiply_rightSection, singularHomologyMap_id]
  rfl

theorem square_homology (a : SingularHomology Space 3) :
    singularHomologyMap square 3 a = a + a := by
  have hd : singularHomologyMap diagonal 3 a = (equivalence one one).symm (a, a) := by
    apply (equivalence one one).injective
    rw [diagonal_homology, LinearEquiv.apply_symm_apply]
  change singularHomologyMap (multiply.comp diagonal) 3 a = a + a
  rw [singularHomologyMap_comp, LinearMap.comp_apply, hd, multiply_homology]

def homologyEquiv : SingularHomology Space 3 ≃ₗ[ℤ] ℤ :=
  (homeomorphHomologyEquiv sphereHomeomorph 3).trans
    (Wikipedia.HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 2)

theorem homologyEquiv_square (a : SingularHomology Space 3) :
    homologyEquiv (singularHomologyMap square 3 a) = 2 * homologyEquiv a := by
  rw [square_homology, map_add, two_mul]

end NoExoticSixSphere.QuaternionSphere
