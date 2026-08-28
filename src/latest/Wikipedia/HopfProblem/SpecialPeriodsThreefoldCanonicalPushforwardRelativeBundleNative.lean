import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeBundleIntrinsic

/-!
# Full native tensor compatibility for the relative canonical line

The tensor product can use the original threefold canonical core itself,
not just its proved transition presentation.  Its original coordinate
changes and local trivializations intertwine with the actual relative
core on the full algebraic tensor product.
-/

noncomputable section

open Bundle Set
open scoped ContDiff Manifold TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.RelativeBundle

open TrianglePeriodFamily.Canonical

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The native presentation intertwines the original canonical transition on every overlap. -/
theorem presentationFiber_coordChange (i j : atlas Model Threefold.Space)
    (x : Threefold.Space) (hi : x ∈ i.val.source) (hj : x ∈ j.val.source)
    (a : Threefold.Canonical.bundle.Fiber x) :
    NativePresentation.fiberEquiv x (Threefold.Canonical.bundle.coordChange i j x a) =
      NativePresentation.transitionBundle.coordChange i j x (NativePresentation.fiberEquiv x a) :=
  by
    change Atlas.jacobian Threefold.Space j i x * id (α := ℂ) a =
      (NativeTransitions.transition Threefold.Space i j x : ℂ) * id (α := ℂ) a
    rw [NativeTransitions.transition_val_eq Threefold.Space i j ⟨hi, hj⟩]

/-- Full transition compatibility with the original canonical core as first tensor factor. -/
theorem nativeTensorEquiv_coordChange (i j : Index) (x : Threefold.Space)
    (hi : x ∈ data.baseSet i) (hj : x ∈ data.baseSet j) :
    (nativeTensorEquiv x).toLinearMap ∘ₗ
        TensorProduct.map (Threefold.Canonical.bundle.coordChange i.1 j.1 x).toLinearMap
          (pullbackBundle.coordChange i.2 j.2 x).toLinearMap =
      (bundle.coordChange i j x).toLinearMap ∘ₗ (nativeTensorEquiv x).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  change nativeTensorEquiv x
      ((Threefold.Canonical.bundle.coordChange i.1 j.1 x a) ⊗ₜ[ℂ]
        (pullbackBundle.coordChange i.2 j.2 x b)) =
    bundle.coordChange i j x (nativeTensorEquiv x (a ⊗ₜ[ℂ] b))
  have h₁ := nativeTensorEquiv_tmul x
    (Threefold.Canonical.bundle.coordChange i.1 j.1 x a)
    (pullbackBundle.coordChange i.2 j.2 x b)
  have h₂ := congrArg
    (fun c : NativePresentation.transitionBundle.Fiber x =>
      fiberTensorEquiv x (c ⊗ₜ[ℂ] (pullbackBundle.coordChange i.2 j.2 x b)))
    (presentationFiber_coordChange i.1 j.1 x hi.1 hj.1 a)
  have h₃ := congrArg (fun L => L ((NativePresentation.fiberEquiv x a) ⊗ₜ[ℂ] b))
    (fiberTensorEquiv_coordChange i j x)
  have h₄ := congrArg (fun c : bundle.Fiber x => bundle.coordChange i j x c)
    (nativeTensorEquiv_tmul x a b).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- The original native local trivializations identify the full tensor fibre coefficient. -/
theorem nativeTensorEquiv_localTriv (i : Index) (x : Threefold.Space)
    (hx : x ∈ data.baseSet i) :
    (bundle.localTriv i).linearMapAt ℂ x ∘ₗ (nativeTensorEquiv x).toLinearMap =
      (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map ((Threefold.Canonical.bundle.localTriv i.1).linearMapAt ℂ x)
          ((pullbackBundle.localTriv i.2).linearMapAt ℂ x) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_toLinearMap,
    TensorProduct.lid_tmul, smul_eq_mul]
  rw [nativeTensorEquiv_tmul]
  have h := congrArg (fun L => L ((NativePresentation.fiberEquiv x a) ⊗ₜ[ℂ] b))
    (fiberTensorEquiv_localTriv i x hx)
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_toLinearMap,
    TensorProduct.lid_tmul, smul_eq_mul] at h
  rw [Trivialization.coe_linearMapAt_of_mem (Threefold.Canonical.bundle.localTriv i.1) hx.1,
    Trivialization.coe_linearMapAt_of_mem (pullbackBundle.localTriv i.2) hx.2]
  rw [Trivialization.coe_linearMapAt_of_mem
      (NativePresentation.transitionBundle.localTriv i.1) hx.1,
    Trivialization.coe_linearMapAt_of_mem (pullbackBundle.localTriv i.2) hx.2] at h
  exact h.trans (congrArg (fun c : ℂ => c * (pullbackBundle.localTriv i.2 ⟨x, b⟩).2)
    (NativePresentation.bundleBiholomorph_localTriv i.1 ⟨x, a⟩ hx.1))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.RelativeBundle
