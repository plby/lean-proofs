import Wikipedia.HopfProblem.HolomorphicPicardTensorCoreBasic
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The actual fibre dual of a native unit-cocycle bundle

The negative cocycle gives the algebraic dual of each original native
fibre.  The equivalence intertwines the genuine contragredient transition
maps and the duals of the original local trivializations.  In particular,
the inverse transition is derived from the actual cocycle, not assumed.
-/

noncomputable section

open Set TopologicalSpace Bundle

namespace Wikipedia.HopfProblem.HolomorphicPicard.TensorCore

open HolomorphicExponentialSheaf HolomorphicPicardNative HolomorphicCharacterBundle
open HolomorphicFunctionSheaf.SphereH1

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} (U : ι → Opens M) (hcover : ∀ x : M, ∃ i : ι, x ∈ U i)
  (c : CechOneCocycle (unitsSheaf I M) U)

/-- Evaluation at the scalar-coordinate unit identifies the actual
algebraic dual of the original native fibre with the negative-cocycle fibre. -/
def fibreDualEquiv (x : M) :
    Module.Dual ℂ ((cocycleCore I M U hcover c).Fiber x) ≃ₗ[ℂ]
      (cocycleCore I M U hcover (-c)).Fiber x :=
  LinearMap.ringLmapEquivSelf ℂ ℂ ℂ

@[simp] theorem fibreDualEquiv_apply (x : M)
    (f : Module.Dual ℂ ((cocycleCore I M U hcover c).Fiber x)) :
    fibreDualEquiv I M U hcover c x f = f (1 : ℂ) := rfl

/-- The dual equivalence retains the genuine evaluation pairing on the
original fibre, not merely the value of a functional on one vector. -/
theorem fibreDualEquiv_pairing (x : M)
    (f : Module.Dual ℂ ((cocycleCore I M U hcover c).Fiber x))
    (v : (cocycleCore I M U hcover c).Fiber x) :
    (id (α := ℂ) (fibreDualEquiv I M U hcover c x f)) * (id (α := ℂ) v) = f v := by
  let φ : ℂ →ₗ[ℂ] ℂ := f
  change φ 1 * (id (α := ℂ) v) = φ (id (α := ℂ) v)
  rw [mul_comm]
  simpa only [smul_eq_mul, mul_one] using
    (map_smul φ (id (α := ℂ) v) (1 : ℂ)).symm

/-- The transpose of the genuine reverse coordinate change is conjugate
to the forward coordinate change of the negative-cocycle bundle. -/
theorem fibreDualEquiv_coordChange (i j : ι) (x : M) (hx : x ∈ U i ⊓ U j) :
    (fibreDualEquiv I M U hcover c x).toLinearMap ∘ₗ
        ((cocycleCore I M U hcover c).coordChange j i x).toLinearMap.dualMap =
      ((cocycleCore I M U hcover (-c)).coordChange i j x).toLinearMap ∘ₗ
        (fibreDualEquiv I M U hcover c x).toLinearMap := by
  apply LinearMap.ext
  intro f
  change f ((cocycleCore I M U hcover c).coordChange j i x (1 : ℂ)) =
    (cocycleCore I M U hcover (-c)).coordChange i j x (f (1 : ℂ))
  simp only [cocycleCore, TransitionData.core_coordChange_apply, mul_one,
    data_neg_transition, Units.val_inv_eq_inv_val]
  rw [data_reverse_transition I M U hcover c i j x hx, Units.val_inv_eq_inv_val]
  simpa only [smul_eq_mul, mul_one] using map_smul (f : ℂ →ₗ[ℂ] ℂ)
    (((cocycleTransitionData I M U hcover c).transition i j x : ℂ)⁻¹) (1 : ℂ)

/-- In every actual local chart, the negative-cocycle coordinate is the
functional's coordinate obtained by precomposing with the inverse original
local trivialization.  This is an equality on the full dual vector space. -/
theorem fibreDualEquiv_localTriv (i : ι) (x : M) (hx : x ∈ U i) :
    ((cocycleCore I M U hcover (-c)).localTriv i).linearMapAt ℂ x ∘ₗ
        (fibreDualEquiv I M U hcover c x).toLinearMap =
      (LinearMap.ringLmapEquivSelf ℂ ℂ ℂ).toLinearMap ∘ₗ
        (((cocycleCore I M U hcover c).localTriv i).symmL ℂ x).toLinearMap.dualMap := by
  apply LinearMap.ext
  intro f
  let φ : ℂ →ₗ[ℂ] ℂ := f
  change ((cocycleCore I M U hcover (-c)).localTriv i).linearMapAt ℂ x
      (φ 1) =
    φ (((cocycleCore I M U hcover c).localTriv i).symmL ℂ x (1 : ℂ))
  rw [Trivialization.coe_linearMapAt_of_mem _ hx, Trivialization.symmL_apply _ hx]
  rw [(cocycleTransitionData I M U hcover c).core_localTriv_fiber_symm i hx]
  simp only [cocycleCore, TransitionData.core_localTriv_apply,
    cocycleTransitionData_indexAt, data_neg_transition, Units.val_inv_eq_inv_val,
    mul_one, id_eq]
  rw [data_reverse_transition I M U hcover c (Classical.choose (hcover x)) i x
    ⟨Classical.choose_spec (hcover x), hx⟩, Units.val_inv_eq_inv_val]
  simpa only [smul_eq_mul, mul_one] using (map_smul φ
    (((cocycleTransitionData I M U hcover c).transition
      (Classical.choose (hcover x)) i x : ℂ)⁻¹) (1 : ℂ)).symm

end Wikipedia.HopfProblem.HolomorphicPicard.TensorCore
