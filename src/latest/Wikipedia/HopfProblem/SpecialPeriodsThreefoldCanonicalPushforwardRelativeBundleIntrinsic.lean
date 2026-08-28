import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeBundleBasic

/-!
# The full intrinsic fibres of the actual relative canonical bundle

Each fibre is the tensor product of the full intrinsic alternating
three-covector space and the full continuous-linear dual of the actual
sphere cotangent space at the image point.  Both factors are identified
using the previously proved native fibre equivalences.
-/

noncomputable section

open Bundle
open scoped ContDiff Manifold TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.RelativeBundle

open TrianglePeriodFamily.Canonical

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The actual tensor of intrinsic top covectors and the dual base cotangent fibre. -/
abbrev IntrinsicFiber (x : Threefold.Space) :=
  Threefold.Canonical.IntrinsicTopCovector x ⊗[ℂ]
    (CanonicalGlobal.SphereCanonical.CotangentSpace (Threefold.projectionSphere x) →L[ℂ] ℂ)

/-- A linear equivalence onto the whole intrinsic tensor product. -/
def fiberIntrinsicEquiv (x : Threefold.Space) : bundle.Fiber x ≃ₗ[ℂ] IntrinsicFiber x :=
  (fiberTensorEquiv x).symm.trans
    (TensorProduct.congr (NativePresentation.dataIntrinsicEquiv x).toLinearEquiv
      (pullbackIntrinsicEquiv x).toLinearEquiv)

/-- Exact interpretation of every elementary tensor of the actual presentation fibres. -/
theorem fiberIntrinsicEquiv_tmul (x : Threefold.Space)
    (a : NativePresentation.transitionBundle.Fiber x) (b : pullbackBundle.Fiber x) :
    fiberIntrinsicEquiv x (fiberTensorEquiv x (a ⊗ₜ[ℂ] b)) =
      NativePresentation.dataIntrinsicEquiv x a ⊗ₜ[ℂ] pullbackIntrinsicEquiv x b := by
  simp only [fiberIntrinsicEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    TensorProduct.congr_tmul, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- The original native canonical vector retains its genuine full three-covector. -/
theorem fiberIntrinsicEquiv_native_tmul (x : Threefold.Space)
    (a : Threefold.Canonical.bundle.Fiber x) (b : pullbackBundle.Fiber x) :
    fiberIntrinsicEquiv x (nativeTensorEquiv x (a ⊗ₜ[ℂ] b)) =
      Threefold.Canonical.intrinsicEquiv x a ⊗ₜ[ℂ] pullbackIntrinsicEquiv x b := by
  rw [nativeTensorEquiv_tmul, fiberIntrinsicEquiv_tmul,
    NativePresentation.dataIntrinsicEquiv_fiberEquiv]

/-- The inverse interprets an arbitrary intrinsic pure tensor through the two actual fibres. -/
theorem fiberIntrinsicEquiv_symm_tmul (x : Threefold.Space)
    (α : Threefold.Canonical.IntrinsicTopCovector x)
    (ℓ : CanonicalGlobal.SphereCanonical.CotangentSpace
      (Threefold.projectionSphere x) →L[ℂ] ℂ) :
    (fiberIntrinsicEquiv x).symm (α ⊗ₜ[ℂ] ℓ) =
      nativeTensorEquiv x (((Threefold.Canonical.intrinsicEquiv x).symm α) ⊗ₜ[ℂ]
        (pullbackIntrinsicEquiv x).symm ℓ) := by
  apply (fiberIntrinsicEquiv x).injective
  rw [LinearEquiv.apply_symm_apply, fiberIntrinsicEquiv_native_tmul,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- This is an equality of maps on the full original tensor product of native fibres. -/
theorem fiberIntrinsicEquiv_nativeTensorEquiv (x : Threefold.Space) :
    (fiberIntrinsicEquiv x).toLinearMap ∘ₗ (nativeTensorEquiv x).toLinearMap =
      TensorProduct.map (Threefold.Canonical.intrinsicEquiv x).toLinearMap
        (pullbackIntrinsicEquiv x).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  exact fiberIntrinsicEquiv_native_tmul x a b

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.RelativeBundle
