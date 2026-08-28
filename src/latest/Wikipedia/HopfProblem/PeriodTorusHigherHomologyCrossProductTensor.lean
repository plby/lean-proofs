import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductHomology

/-!
# Tensor-product forms of the actual edge and homology cross products

These are the tensor-product lifts of the already constructed bilinear maps.
The chain modules and homology objects are Mathlib's actual singular ones.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz
open scoped TensorProduct

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual chain cross product as a map from the tensor product of chain modules. -/
def crossProductEdgeTensor (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    Chains X 1 ⊗[ℤ] Chains Y n →ₗ[ℤ] Chains (X × Y) (n + 1) :=
  TensorProduct.lift (crossProductEdge X Y n)

@[simp] theorem crossProductEdgeTensor_tmul (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : Chains X 1) (b : Chains Y n) :
    crossProductEdgeTensor X Y n (a ⊗ₜ[ℤ] b) = crossProductEdge X Y n a b := rfl

/-- The induced actual homology cross product in tensor-product form. -/
def crossProductHomologyTensor (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    (singularComplex X).homology 1 ⊗[ℤ] (singularComplex Y).homology n →ₗ[ℤ]
      (singularComplex (X × Y)).homology (n + 1) :=
  TensorProduct.lift (crossProductHomology X Y n)

@[simp] theorem crossProductHomologyTensor_tmul (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : (singularComplex X).homology 1) (b : (singularComplex Y).homology n) :
    crossProductHomologyTensor X Y n (a ⊗ₜ[ℤ] b) = crossProductHomology X Y n a b := rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
