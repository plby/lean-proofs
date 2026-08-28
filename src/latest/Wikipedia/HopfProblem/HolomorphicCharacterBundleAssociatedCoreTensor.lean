import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedCore
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor products of character line-bundle cocycles

The bundle of a product character has the product transition cocycle.
Multiplication of scalar fibre coordinates induces a genuine algebraic
tensor-product equivalence on every fibre. The equivalence intertwines
the tensor products of the original transition maps and the actual local
trivializations. Thus the character product has the usual tensor-bundle
interpretation, without imposing a global trivialization on either factor.
-/

noncomputable section

open Set Bundle
open scoped TensorProduct

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle.AssociatedCore

variable {G A B : Type*} [Group G] [MulAction G A]
    [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : IsQuotientCoveringMap q G) (χ ψ : G →* ℂˣ)

@[simp] theorem data_mul_transition (i j x : B) :
    (data hq (χ * ψ)).transition i j x =
      (data hq χ).transition i j x * (data hq ψ).transition i j x := rfl

@[simp] theorem data_one_transition (i j x : B) :
    (data hq (1 : G →* ℂˣ)).transition i j x = 1 := rfl

@[simp] theorem data_pow_transition (n : ℕ) (i j x : B) :
    (data hq (χ ^ n)).transition i j x = ((data hq χ).transition i j x) ^ n := by
  simp only [data_transition, MonoidHom.pow_apply]

/-- The product-character fibre is the algebraic tensor product of the
two original fibres, by scalar multiplication. -/
def fibreTensorEquiv (b : B) :
    (data hq χ).core.Fiber b ⊗[ℂ] (data hq ψ).core.Fiber b ≃ₗ[ℂ]
      (data hq (χ * ψ)).core.Fiber b :=
  TensorProduct.lid ℂ ℂ

@[simp] theorem fibreTensorEquiv_tmul (b : B)
    (z : (data hq χ).core.Fiber b) (w : (data hq ψ).core.Fiber b) :
    fibreTensorEquiv hq χ ψ b (z ⊗ₜ[ℂ] w) = (id (α := ℂ) z) * (id (α := ℂ) w) :=
  TensorProduct.lid_tmul (R := ℂ) (M := ℂ) w z

/-- The tensor product of the two transition maps is conjugate to the
transition map of the product character. This is an equality of linear
maps on the full tensor product, not just a rule on elementary tensors. -/
theorem fibreTensorEquiv_coordChange (i j b : B) :
    (fibreTensorEquiv hq χ ψ b).toLinearMap ∘ₗ
        TensorProduct.map ((data hq χ).core.coordChange i j b).toLinearMap
          ((data hq ψ).core.coordChange i j b).toLinearMap =
      ((data hq (χ * ψ)).core.coordChange i j b).toLinearMap ∘ₗ
        (fibreTensorEquiv hq χ ψ b).toLinearMap := by
  apply TensorProduct.ext'
  intro z w
  change (TensorProduct.lid ℂ ℂ)
      (((data hq χ).core.coordChange i j b z) ⊗ₜ[ℂ]
        ((data hq ψ).core.coordChange i j b w)) =
    (data hq (χ * ψ)).core.coordChange i j b ((TensorProduct.lid ℂ ℂ) (z ⊗ₜ[ℂ] w))
  simp only [TensorProduct.lid_tmul, smul_eq_mul, TransitionData.core_coordChange_apply,
    data_mul_transition, Units.val_mul]
  ring

/-- Every actual local trivialization sends the fibre tensor equivalence
to multiplication in the two scalar chart coordinates. -/
theorem fibreTensorEquiv_localTriv (i b : B) (hb : b ∈ baseSet hq i) :
    ((data hq (χ * ψ)).core.localTriv i).linearMapAt ℂ b ∘ₗ
        (fibreTensorEquiv hq χ ψ b).toLinearMap =
      (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map (((data hq χ).core.localTriv i).linearMapAt ℂ b)
          (((data hq ψ).core.localTriv i).linearMapAt ℂ b) := by
  apply TensorProduct.ext'
  intro z w
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_toLinearMap,
    fibreTensorEquiv_tmul]
  rw [Trivialization.coe_linearMapAt_of_mem _ hb,
    Trivialization.coe_linearMapAt_of_mem _ hb,
    Trivialization.coe_linearMapAt_of_mem _ hb]
  simp only [TransitionData.core_localTriv_apply, data_indexAt,
    data_mul_transition, Units.val_mul, TensorProduct.lid_tmul, smul_eq_mul, id_eq]
  ring

end Wikipedia.HopfProblem.HolomorphicCharacterBundle.AssociatedCore
