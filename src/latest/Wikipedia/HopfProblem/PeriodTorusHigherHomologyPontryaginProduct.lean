import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductHomology

/-!
# Genuine low-degree Pontryagin products

The product is the actual singular-homology cross product followed by the
actual singular-homology map of addition. Its bilinearity and its evaluation
on genuine cycles are inherited from those two constructed maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin

open FirstHurewicz SingularMayerVietoris ModuleHomology PeriodTorusHigherHomology

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

variable (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

/-- The actual Pontryagin product with a degree-one left input. -/
def product (n : ℕ) :
    SingularHomology G 1 →ₗ[ℤ] SingularHomology G n →ₗ[ℤ] SingularHomology G (n + 1) :=
  integerBilinearPostcompose (crossProductHomology G G n)
    (singularHomologyMap (additionMap G) (n + 1))

@[simp] theorem product_apply (n : ℕ)
    (a : SingularHomology G 1) (b : SingularHomology G n) :
    product G n a b = singularHomologyMap (additionMap G) (n + 1)
      (crossProductHomology G G n a b) := rfl

abbrev product11 :
    SingularHomology G 1 →ₗ[ℤ] SingularHomology G 1 →ₗ[ℤ] SingularHomology G 2 :=
  product G 1

abbrev product12 :
    SingularHomology G 1 →ₗ[ℤ] SingularHomology G 2 →ₗ[ℤ] SingularHomology G 3 :=
  product G 2

/-- The actual cycle whose class computes the Pontryagin product. -/
def productCycles (n : ℕ) :
    Cycle (singularComplex G) 1 →ₗ[ℤ] Cycle (singularComplex G) n →ₗ[ℤ]
      Cycle (singularComplex G) (n + 1) :=
  integerBilinearPostcompose (crossProductCycles G G n)
    (mapCycles (singularChainMap (additionMap G)) (n + 1))

@[simp] theorem productCycles_val (n : ℕ)
    (a : Cycle (singularComplex G) 1) (b : Cycle (singularComplex G) n) :
    (productCycles G n a b).1 =
      inducedChain (additionMap G) (n + 1) (crossProductEdge G G n a.1 b.1) := by
  rw [productCycles, integerBilinearPostcompose_apply, mapCycles_val, crossProductCycles_val]

/-- Evaluation on actual cycle classes uses the actual chain cross product. -/
@[simp] theorem product_cycleClass (n : ℕ)
    (a : Cycle (singularComplex G) 1) (b : Cycle (singularComplex G) n) :
    product G n (cycleClass (singularComplex G) 1 a) (cycleClass (singularComplex G) n b) =
      cycleClass (singularComplex G) (n + 1) (productCycles G n a b) := by
  rw [product_apply, crossProductHomology_cycleClass]
  exact homologyMap_cycleClass (singularChainMap (additionMap G)) (n + 1)
    (crossProductCycles G G n a b)

/-- The genuine right-associated product of three degree-one homology classes. -/
def tripleProduct :
    SingularHomology G 1 →ₗ[ℤ] SingularHomology G 1 →ₗ[ℤ]
      SingularHomology G 1 →ₗ[ℤ] SingularHomology G 3 where
  toFun a := integerBilinearPostcompose (product11 G) (product12 G a)
  map_add' a b := by
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro d
    exact congrArg (fun f : SingularHomology G 2 →ₗ[ℤ] SingularHomology G 3 =>
      f (product11 G c d)) ((product12 G).map_add a b)
  map_smul' r a := by
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro d
    exact congrArg (fun f : SingularHomology G 2 →ₗ[ℤ] SingularHomology G 3 =>
      f (product11 G c d)) ((product12 G).map_smul r a)

@[simp] theorem tripleProduct_apply
    (a b c : SingularHomology G 1) :
    tripleProduct G a b c = product12 G a (product11 G b c) := rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin
