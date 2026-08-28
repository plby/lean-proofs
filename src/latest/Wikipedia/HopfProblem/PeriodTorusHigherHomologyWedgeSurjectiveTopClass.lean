import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusProductDecomposition
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjectiveAlgebra

/-!
# Actual coordinate-subtorus top classes lie in exterior-product ranges

The proved positive-circle decomposition writes the actual top class of a
two-torus as a product of degree-one classes, and that of a three-torus as
a triple product. Naturality then places their images under any continuous
additive map in the ranges of the actual exterior-product maps, whenever
the chosen lattice marking covers first homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomologyPontryagin

/-- The genuine normalized two-torus top class is a product of two actual
degree-one homology classes. -/
theorem productTorusTopClass_two_is_product :
    ∃ a b : SingularHomology (ProductTorus 2) 1,
      productTorusTopClass 2 = product11 (ProductTorus 2) a b := by
  refine ⟨loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1)),
    singularHomologyMap (torusTailMap 1) 1 (productTorusTopClass 1), ?_⟩
  exact productTorusTopClass_succ_product 1

/-- The genuine normalized three-torus top class is a product of three
actual degree-one homology classes. -/
theorem productTorusTopClass_three_is_tripleProduct :
    ∃ a b c : SingularHomology (ProductTorus 3) 1,
      productTorusTopClass 3 = tripleProduct (ProductTorus 3) a b c := by
  obtain ⟨a, b, hab⟩ := productTorusTopClass_two_is_product
  refine ⟨loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 0 1)),
    singularHomologyMap (torusTailMap 2) 1 a,
    singularHomologyMap (torusTailMap 2) 1 b, ?_⟩
  rw [tripleProduct_apply, productTorusTopClass_succ_product 2, hab,
    product_natural (torusTailMap 2) (torusTailMap_add 2) 1]

variable {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [Module.IsTorsionFree ℤ (SingularHomology G 2)]

/-- An additive image of the actual two-torus top class lies in the range
of the actual degree-two wedge map of any surjective first-homology marking. -/
theorem map_topClass_two_mem_range_latticeWedgeTwo
    (c : Lattice →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (f : C(ProductTorus 2, G)) (hf : ∀ x y, f (x + y) = f x + f y) :
    singularHomologyMap f 2 (productTorusTopClass 2) ∈
      LinearMap.range (latticeWedgeTwo G c) := by
  obtain ⟨a, b, hab⟩ := productTorusTopClass_two_is_product
  rw [hab, product_natural f hf 1]
  exact product11_mem_range_latticeWedgeTwo G c hc _ _

/-- An additive image of the actual three-torus top class lies in the range
of the actual degree-three wedge map of any surjective first-homology marking. -/
theorem map_topClass_three_mem_range_latticeWedgeThree
    (c : Lattice →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (f : C(ProductTorus 3, G)) (hf : ∀ x y, f (x + y) = f x + f y) :
    singularHomologyMap f 3 (productTorusTopClass 3) ∈
      LinearMap.range (latticeWedgeThree G c) := by
  obtain ⟨a, b, d, habd⟩ := productTorusTopClass_three_is_tripleProduct
  rw [habd, tripleProduct_natural f hf]
  exact tripleProduct_mem_range_latticeWedgeThree G c hc _ _ _

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
