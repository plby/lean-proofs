import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeBundleBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalNativeCanonical
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleTensor

/-!
# The actual relative canonical line bundle

The first factor is the native alternating-cotangent canonical bundle of
the original threefold, through its proved native transition presentation.
The second is the actual pullback of the continuous-linear dual of the
sphere's native cotangent line.  Their product cocycle carries its original
native bundle topology and analytic atlas.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.RelativeBundle

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

/-- The paired original threefold and sphere chart indices. -/
abbrev Index := atlas Model Threefold.Space × Bool

/-- The genuine tensor cocycle defining `K_X ⊗ f^*(K_{ℙ¹}^∨)`. -/
def data : HolomorphicCharacterBundle.TransitionData Threefold.Space Index :=
  tensor NativePresentation.transitionData pullbackData

/-- The original native core of this tensor cocycle. -/
abbrev bundle := data.core

@[simp] theorem data_baseSet (i : Index) :
    data.baseSet i = NativePresentation.transitionData.baseSet i.1 ∩
      Threefold.projectionSphere ⁻¹' baseData.baseSet i.2 := rfl

@[simp] theorem data_indexAt (x : Threefold.Space) :
    data.indexAt x =
      (NativePresentation.transitionData.indexAt x,
        baseData.indexAt (Threefold.projectionSphere x)) := rfl

@[simp] theorem data_transition (i j : Index) (x : Threefold.Space) :
    data.transition i j x = NativePresentation.transitionData.transition i.1 j.1 x *
      baseData.transition i.2 j.2 (Threefold.projectionSphere x) := rfl

instance data_isHolomorphic : data.IsHolomorphic IF :=
  tensor_isHolomorphic NativePresentation.transitionData pullbackData IF

theorem bundle_holomorphic : ContMDiffVectorBundle ω ℂ bundle.Fiber IF :=
  data.core_contMDiffVectorBundle IF

theorem bundle_totalSpace_isManifold :
    IsManifold ((IF).prod 𝓘(ℂ)) ω bundle.TotalSpace := data.core_totalSpace_isManifold IF

theorem bundle_fibre_rank_one (x : Threefold.Space) :
    Module.finrank ℂ (bundle.Fiber x) = 1 := Module.finrank_self ℂ

/-- The whole tensor product of the two actual presentation fibres. -/
def fiberTensorEquiv (x : Threefold.Space) :
    NativePresentation.transitionBundle.Fiber x ⊗[ℂ] pullbackBundle.Fiber x ≃ₗ[ℂ]
      bundle.Fiber x := fibreTensorEquiv NativePresentation.transitionData pullbackData x

@[simp] theorem fiberTensorEquiv_tmul (x : Threefold.Space)
    (a : NativePresentation.transitionBundle.Fiber x) (b : pullbackBundle.Fiber x) :
    fiberTensorEquiv x (a ⊗ₜ[ℂ] b) = id (α := ℂ) a * id (α := ℂ) b :=
  fibreTensorEquiv_tmul NativePresentation.transitionData pullbackData x a b

/-- On the entire tensor product, the paired transition is the tensor of the two transitions. -/
theorem fiberTensorEquiv_coordChange (i j : Index) (x : Threefold.Space) :
    (fiberTensorEquiv x).toLinearMap ∘ₗ
        TensorProduct.map
          (NativePresentation.transitionBundle.coordChange i.1 j.1 x).toLinearMap
          (pullbackBundle.coordChange i.2 j.2 x).toLinearMap =
      (bundle.coordChange i j x).toLinearMap ∘ₗ (fiberTensorEquiv x).toLinearMap :=
  fibreTensorEquiv_coordChange NativePresentation.transitionData pullbackData i j x

/-- Full native local-trivialization compatibility, not only a rule on pure tensors. -/
theorem fiberTensorEquiv_localTriv (i : Index) (x : Threefold.Space)
    (hx : x ∈ data.baseSet i) :
    (bundle.localTriv i).linearMapAt ℂ x ∘ₗ (fiberTensorEquiv x).toLinearMap =
      (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map
          ((NativePresentation.transitionBundle.localTriv i.1).linearMapAt ℂ x)
          ((pullbackBundle.localTriv i.2).linearMapAt ℂ x) :=
  fibreTensorEquiv_localTriv NativePresentation.transitionData pullbackData i x hx

/-- The first factor can equivalently be the original native canonical fibre itself. -/
def nativeTensorEquiv (x : Threefold.Space) :
    Threefold.Canonical.bundle.Fiber x ⊗[ℂ] pullbackBundle.Fiber x ≃ₗ[ℂ] bundle.Fiber x :=
  (TensorProduct.congr (NativePresentation.fiberEquiv x).toLinearEquiv
    (LinearEquiv.refl ℂ (pullbackBundle.Fiber x))).trans (fiberTensorEquiv x)

theorem nativeTensorEquiv_tmul (x : Threefold.Space)
    (a : Threefold.Canonical.bundle.Fiber x) (b : pullbackBundle.Fiber x) :
    nativeTensorEquiv x (a ⊗ₜ[ℂ] b) =
      fiberTensorEquiv x ((NativePresentation.fiberEquiv x a) ⊗ₜ[ℂ] b) := by
  simp only [nativeTensorEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    ContinuousLinearEquiv.coe_toLinearEquiv, LinearEquiv.refl_apply]

/-- The canonical transition factor is the literal reverse derivative of the original chart. -/
theorem data_transition_fderiv (i j : Index) {x : Threefold.Space}
    (hi : x ∈ data.baseSet i) (hj : x ∈ data.baseSet j) :
    (data.transition i j x : ℂ) =
      LinearMap.det (fderiv ℂ (i.1.val ∘ j.1.val.symm) (j.1.val x)).toLinearMap *
        (baseData.transition i.2 j.2 (Threefold.projectionSphere x) : ℂ) := by
  rw [data_transition, Units.val_mul]
  exact congrArg
    (fun c : ℂ => c * (baseData.transition i.2 j.2 (Threefold.projectionSphere x) : ℂ))
      (NativeTransitions.transition_val_eq_fderiv Threefold.Space i.1 j.1 ⟨hi.1, hj.1⟩)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.RelativeBundle
