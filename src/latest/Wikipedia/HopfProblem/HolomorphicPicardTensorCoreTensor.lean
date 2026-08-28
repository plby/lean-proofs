import Wikipedia.HopfProblem.HolomorphicPicardTensorCoreBasic
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Actual fibre tensor products of native cocycle bundles

The native bundle glued from the sum of two actual unit cocycles has the
genuine algebraic tensor product of their fibres.  The scalar-coordinate
equivalence intertwines the full linear transition maps and each original
local trivialization.  This establishes the geometric tensor interpretation
without transporting a group law from sheaf cohomology.
-/

noncomputable section

open Set TopologicalSpace Bundle
open scoped TensorProduct

namespace Wikipedia.HopfProblem.HolomorphicPicard.TensorCore

open HolomorphicExponentialSheaf HolomorphicPicardNative HolomorphicCharacterBundle
open HolomorphicFunctionSheaf.SphereH1

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} (U : ι → Opens M) (hcover : ∀ x : M, ∃ i : ι, x ∈ U i)
  (c d : CechOneCocycle (unitsSheaf I M) U)

/-- A genuine linear equivalence from the tensor product of the original
native fibres to the fibre of the sum-cocycle bundle. -/
def fibreTensorEquiv (x : M) :
    (cocycleCore I M U hcover c).Fiber x ⊗[ℂ]
        (cocycleCore I M U hcover d).Fiber x ≃ₗ[ℂ]
      (cocycleCore I M U hcover (c + d)).Fiber x :=
  TensorProduct.lid ℂ ℂ

@[simp] theorem fibreTensorEquiv_tmul (x : M)
    (z : (cocycleCore I M U hcover c).Fiber x)
    (w : (cocycleCore I M U hcover d).Fiber x) :
    fibreTensorEquiv I M U hcover c d x (z ⊗ₜ[ℂ] w) =
      (id (α := ℂ) z) * (id (α := ℂ) w) :=
  TensorProduct.lid_tmul (R := ℂ) (M := ℂ) w z

/-- Compatibility is an equality of linear maps on the full tensor
product, not only an identity on elementary tensors. -/
theorem fibreTensorEquiv_coordChange (i j : ι) (x : M) :
    (fibreTensorEquiv I M U hcover c d x).toLinearMap ∘ₗ
        TensorProduct.map ((cocycleCore I M U hcover c).coordChange i j x).toLinearMap
          ((cocycleCore I M U hcover d).coordChange i j x).toLinearMap =
      ((cocycleCore I M U hcover (c + d)).coordChange i j x).toLinearMap ∘ₗ
        (fibreTensorEquiv I M U hcover c d x).toLinearMap := by
  apply TensorProduct.ext'
  intro z w
  change (TensorProduct.lid ℂ ℂ)
      (((cocycleCore I M U hcover c).coordChange i j x z) ⊗ₜ[ℂ]
        ((cocycleCore I M U hcover d).coordChange i j x w)) =
    (cocycleCore I M U hcover (c + d)).coordChange i j x
      ((TensorProduct.lid ℂ ℂ) (z ⊗ₜ[ℂ] w))
  simp only [cocycleCore, TensorProduct.lid_tmul, smul_eq_mul,
    TransitionData.core_coordChange_apply, data_add_transition, Units.val_mul]
  ring

/-- Every actual local trivialization sends the fibre tensor map to
multiplication of the two original scalar chart coordinates. -/
theorem fibreTensorEquiv_localTriv (i : ι) (x : M) (hx : x ∈ U i) :
    ((cocycleCore I M U hcover (c + d)).localTriv i).linearMapAt ℂ x ∘ₗ
        (fibreTensorEquiv I M U hcover c d x).toLinearMap =
      (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map (((cocycleCore I M U hcover c).localTriv i).linearMapAt ℂ x)
          (((cocycleCore I M U hcover d).localTriv i).linearMapAt ℂ x) := by
  apply TensorProduct.ext'
  intro z w
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_toLinearMap,
    fibreTensorEquiv_tmul]
  rw [Trivialization.coe_linearMapAt_of_mem _ hx,
    Trivialization.coe_linearMapAt_of_mem _ hx,
    Trivialization.coe_linearMapAt_of_mem _ hx]
  simp only [cocycleCore, TransitionData.core_localTriv_apply,
    cocycleTransitionData_indexAt, data_add_transition, Units.val_mul,
    TensorProduct.lid_tmul, smul_eq_mul, id_eq]
  ring

end Wikipedia.HopfProblem.HolomorphicPicard.TensorCore
