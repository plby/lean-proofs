import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundlePullback
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-!
# The cocycle pullback is the native pullback bundle

The line bundle obtained by pulling back its transition data is analytically
identified with Mathlib's actual pullback of the original native bundle.
Both maps preserve the base point and are the identity on the native complex
fibres.  Their regularity is checked in the two original preferred bundle
charts, whose scalar coordinates agree exactly.  The comparison also commutes
with the native map from the pullback total space to the original total space.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback

open HolomorphicCharacterBundle CanonicalGlobalLineBundle
  PeriodTorusLineBundleClassificationNative

variable {M N ι : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {E H E' H' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
    [ChartedSpace H M] [ChartedSpace H' N]
    (A : TransitionData N ι) (I : ModelWithCorners ℂ E H)
    (J : ModelWithCorners ℂ E' H') (f : ContMDiffMap I J M N ω)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The native fibres of the two pullback constructions have the same
preferred complex coordinate. -/
def pullbackNativeFiberEquiv (x : M) :
    (pullback A f f.contMDiff.continuous).core.Fiber x ≃L[ℂ]
      ((f : M → N) *ᵖ A.core.Fiber) x :=
  ContinuousLinearEquiv.refl ℂ ℂ

@[simp] theorem pullbackNativeFiberEquiv_apply (x : M)
    (v : (pullback A f f.contMDiff.continuous).core.Fiber x) :
    pullbackNativeFiberEquiv A I J f x v = id (α := ℂ) v := rfl

/-- The identity in the preferred fibre coordinates, with the native
pullback topology and charted-space structure on its target. -/
def pullbackNativeMap (v : (pullback A f f.contMDiff.continuous).core.TotalSpace) :
    TotalSpace ℂ ((f : M → N) *ᵖ A.core.Fiber) :=
  ⟨v.proj, pullbackNativeFiberEquiv A I J f v.proj v.2⟩

/-- The reverse identity uses the original pulled-back cocycle bundle. -/
def pullbackNativeInvMap (v : TotalSpace ℂ ((f : M → N) *ᵖ A.core.Fiber)) :
    (pullback A f f.contMDiff.continuous).core.TotalSpace :=
  ⟨v.proj, (pullbackNativeFiberEquiv A I J f v.proj).symm v.2⟩

@[simp] theorem pullbackNativeMap_apply
    (v : (pullback A f f.contMDiff.continuous).core.TotalSpace) :
    pullbackNativeMap A I J f v = ⟨v.proj, id (α := ℂ) v.2⟩ := rfl

@[simp] theorem pullbackNativeInvMap_apply
    (v : TotalSpace ℂ ((f : M → N) *ᵖ A.core.Fiber)) :
    pullbackNativeInvMap A I J f v = ⟨v.proj, id (α := ℂ) v.2⟩ := rfl

/-- The actual preferred trivializations agree under the fibre identity. -/
theorem pullbackNativeMap_trivializationAt (x : M)
    (v : (pullback A f f.contMDiff.continuous).core.TotalSpace) :
    trivializationAt ℂ ((f : M → N) *ᵖ A.core.Fiber) x
        (pullbackNativeMap A I J f v) =
      trivializationAt ℂ (pullback A f f.contMDiff.continuous).core.Fiber x v := rfl

theorem pullbackNativeInvMap_trivializationAt (x : M)
    (v : TotalSpace ℂ ((f : M → N) *ᵖ A.core.Fiber)) :
    trivializationAt ℂ (pullback A f f.contMDiff.continuous).core.Fiber x
        (pullbackNativeInvMap A I J f v) =
      trivializationAt ℂ ((f : M → N) *ᵖ A.core.Fiber) x v := rfl

/-- The comparison is analytic for the original bundle atlases. -/
theorem pullbackNativeMap_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (pullbackNativeMap A I J f) := by
  intro v
  have hid : ContMDiffAt (I.prod I₁) (I.prod I₁) ω id v := contMDiffAt_id
  rw [Bundle.contMDiffAt_totalSpace] at hid ⊢
  exact hid

/-- The inverse comparison is analytic for the native pullback atlas. -/
theorem pullbackNativeInvMap_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (pullbackNativeInvMap A I J f) := by
  intro v
  have hid : ContMDiffAt (I.prod I₁) (I.prod I₁) ω id v := contMDiffAt_id
  rw [Bundle.contMDiffAt_totalSpace] at hid ⊢
  exact hid

/-- The pulled-back cocycle bundle and the actual native pullback are
analytically and fibrewise complex-linearly isomorphic. -/
def pullbackNativeIso :
    AnalyticBundleIso I (pullback A f f.contMDiff.continuous).core.Fiber
      ((f : M → N) *ᵖ A.core.Fiber) :=
  AnalyticBundleIso.ofFiberEquiv
    (fun x => (pullbackNativeFiberEquiv A I J f x).toLinearEquiv)
    (pullbackNativeMap_holomorphic A I J f) (pullbackNativeInvMap_holomorphic A I J f)

@[simp] theorem pullbackNativeIso_apply
    (v : (pullback A f f.contMDiff.continuous).core.TotalSpace) :
    (pullbackNativeIso A I J f).diffeomorph v =
      ⟨v.proj, id (α := ℂ) v.2⟩ := rfl

@[simp] theorem pullbackNativeIso_symm_apply
    (v : TotalSpace ℂ ((f : M → N) *ᵖ A.core.Fiber)) :
    (pullbackNativeIso A I J f).diffeomorph.symm v =
      ⟨v.proj, id (α := ℂ) v.2⟩ := rfl

/-- The comparison commutes pointwise with the actual native pullback lift. -/
@[simp] theorem pullbackNativeIso_lift
    (v : (pullback A f f.contMDiff.continuous).core.TotalSpace) :
    Bundle.Pullback.lift (f : M → N) ((pullbackNativeIso A I J f).diffeomorph v) =
      pullbackTotalMap A f f.contMDiff.continuous v := rfl

/-- The full total-space diagram uses Mathlib's native pullback lift. -/
theorem pullbackNativeIso_lift_comp :
    Bundle.Pullback.lift (f : M → N) ∘ (pullbackNativeIso A I J f).diffeomorph =
      pullbackTotalMap A f f.contMDiff.continuous := rfl

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback
