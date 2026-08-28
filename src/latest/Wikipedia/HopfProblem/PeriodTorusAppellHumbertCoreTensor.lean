import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCore
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertFactorMultiplicativity
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor products of the actual integral Appell--Humbert bundles

Adding two integral type-`(1,1)` forms multiplies their genuine transition
cocycles. Scalar multiplication induces an algebraic tensor-product
equivalence on each pair of fibres. The equivalence intertwines the full
linear coordinate-change maps and every actual local trivialization.
Integer scaling gives the corresponding integer power of each transition.
No classification of arbitrary line bundles is asserted.
-/

noncomputable section

open Set Bundle
open scoped TensorProduct

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core

open PeriodTorusTypeOneOne HolomorphicCharacterBundle

variable (p : PeriodDomain) (E F : Fin 6 → ℤ)
  (hE : IsTypeOneOne (tangentForm p E)) (hF : IsTypeOneOne (tangentForm p F))

/-- Addition of the integral forms multiplies the actual transition functions. -/
@[simp] theorem data_add_coefficients_transition (i j x : p.Torus) :
    (data (integralFactor p (E + F) (integralType_add p E F hE hF))).transition i j x =
      (data (integralFactor p E hE)).transition i j x *
        (data (integralFactor p F hF)).transition i j x :=
  integralFactor_add_coefficients p E F hE hF _ _

/-- Every integer scaling, including a negative one, gives the corresponding
power of the genuine nonzero transition function. -/
@[simp] theorem data_zsmul_transition (n : ℤ) (i j x : p.Torus) :
    (data (integralFactor p (n • E) (integralType_zsmul p n E hE))).transition i j x =
      ((data (integralFactor p E hE)).transition i j x) ^ n :=
  integralFactor_zsmul p n E hE _ _

/-- The sum-form fibre is the genuine algebraic tensor product of the two
original fibres, by scalar multiplication. -/
def fibreTensorEquiv (b : p.Torus) :
    (data (integralFactor p E hE)).core.Fiber b ⊗[ℂ]
      (data (integralFactor p F hF)).core.Fiber b ≃ₗ[ℂ]
        (data (integralFactor p (E + F) (integralType_add p E F hE hF))).core.Fiber b :=
  TensorProduct.lid ℂ ℂ

@[simp] theorem fibreTensorEquiv_tmul (b : p.Torus)
    (z : (data (integralFactor p E hE)).core.Fiber b)
    (w : (data (integralFactor p F hF)).core.Fiber b) :
    fibreTensorEquiv p E F hE hF b (z ⊗ₜ[ℂ] w) =
      (id (α := ℂ) z) * (id (α := ℂ) w) :=
  TensorProduct.lid_tmul (R := ℂ) (M := ℂ) w z

/-- Intertwining holds on the full tensor product as an equality of linear
maps, not only on elementary tensors. -/
theorem fibreTensorEquiv_coordChange (i j b : p.Torus) :
    (fibreTensorEquiv p E F hE hF b).toLinearMap ∘ₗ
        TensorProduct.map
          ((data (integralFactor p E hE)).core.coordChange i j b).toLinearMap
          ((data (integralFactor p F hF)).core.coordChange i j b).toLinearMap =
      ((data (integralFactor p (E + F) (integralType_add p E F hE hF))).core.coordChange
          i j b).toLinearMap ∘ₗ
        (fibreTensorEquiv p E F hE hF b).toLinearMap := by
  apply TensorProduct.ext'
  intro z w
  change (TensorProduct.lid ℂ ℂ)
      (((data (integralFactor p E hE)).core.coordChange i j b z) ⊗ₜ[ℂ]
        ((data (integralFactor p F hF)).core.coordChange i j b w)) =
    (data (integralFactor p (E + F) (integralType_add p E F hE hF))).core.coordChange
      i j b ((TensorProduct.lid ℂ ℂ) (z ⊗ₜ[ℂ] w))
  simp only [TensorProduct.lid_tmul, smul_eq_mul, TransitionData.core_coordChange_apply]
  rw [data_add_coefficients_transition p E F hE hF i j b, Units.val_mul]
  ring

/-- Every original local trivialization identifies the tensor equivalence
with multiplication of its two genuine scalar fibre coordinates. -/
theorem fibreTensorEquiv_localTriv (i b : p.Torus) (hb : b ∈ baseSet p i) :
    ((data (integralFactor p (E + F)
        (integralType_add p E F hE hF))).core.localTriv i).linearMapAt ℂ b ∘ₗ
      (fibreTensorEquiv p E F hE hF b).toLinearMap =
      (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map
          (((data (integralFactor p E hE)).core.localTriv i).linearMapAt ℂ b)
          (((data (integralFactor p F hF)).core.localTriv i).linearMapAt ℂ b) := by
  apply TensorProduct.ext'
  intro z w
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_toLinearMap,
    fibreTensorEquiv_tmul]
  rw [Trivialization.coe_linearMapAt_of_mem _ hb,
    Trivialization.coe_linearMapAt_of_mem _ hb,
    Trivialization.coe_linearMapAt_of_mem _ hb]
  simp only [TransitionData.core_localTriv_apply, data_indexAt,
    TensorProduct.lid_tmul, smul_eq_mul, id_eq]
  rw [data_add_coefficients_transition p E F hE hF b i b, Units.val_mul]
  ring

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core
