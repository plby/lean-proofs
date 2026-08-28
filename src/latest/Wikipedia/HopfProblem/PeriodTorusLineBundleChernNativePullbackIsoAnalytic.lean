import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-!
# Analytic total-space maps on native pullback bundles

The native pullback lift is analytic for the original preferred bundle charts.
Consequently, pulling back the fibre maps of an actual analytic bundle
isomorphism gives an analytic map on the native pullback total spaces.
Neither assertion assumes a smooth vector-bundle structure or a trivialization.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {E H E' H' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
    [ChartedSpace H M] [ChartedSpace H' N]
    (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')

local notation "I₁" => modelWithCornersSelf ℂ ℂ

section Lift

variable (V : N → Type*) [∀ x, Nonempty (V x)] [∀ x, TopologicalSpace (V x)]
    [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V]
    (f : ContMDiffMap I J M N ω)

/-- The native map from the pullback total space to the original total space
is analytic. Its scalar chart component is the identity's chart component. -/
theorem pullbackLift_holomorphic :
    ContMDiff (I.prod I₁) (J.prod I₁) ω
      (Bundle.Pullback.lift (F := ℂ) (E := V) (f : M → N)) := by
  intro v
  have hid : ContMDiffAt (I.prod I₁) (I.prod I₁) ω id v := contMDiffAt_id
  rw [Bundle.contMDiffAt_totalSpace] at hid ⊢
  exact ⟨f.contMDiff.contMDiffAt.comp v hid.1, hid.2⟩

end Lift

namespace AnalyticBundleIso

variable {I J} {V W : N → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W]
    (e : AnalyticBundleIso J V W) (f : ContMDiffMap I J M N ω)

/-- The actual fibre map of an analytic bundle isomorphism, pulled back along
an analytic map of bases, with the native pullback total-space topologies. -/
def pullbackTotalMap (v : TotalSpace ℂ ((f : M → N) *ᵖ V)) :
    TotalSpace ℂ ((f : M → N) *ᵖ W) :=
  ⟨v.proj, e.fiberEquiv (f v.proj) v.2⟩

@[simp] theorem pullbackTotalMap_apply (v : TotalSpace ℂ ((f : M → N) *ᵖ V)) :
    pullbackTotalMap e f v = ⟨v.proj, e.fiberEquiv (f v.proj) v.2⟩ := rfl

/-- The pulled-back total map commutes with the actual native pullback lifts. -/
theorem pullbackTotalMap_lift (v : TotalSpace ℂ ((f : M → N) *ᵖ V)) :
    Bundle.Pullback.lift (f : M → N) (pullbackTotalMap e f v) =
      e.diffeomorph (Bundle.Pullback.lift (f : M → N) v) :=
  (e.map_fiber (f v.proj) v.2).symm

/-- Analyticity follows from the original total-space diffeomorphism and the
native pullback lift, using the original preferred bundle charts. -/
theorem pullbackTotalMap_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (pullbackTotalMap e f) := by
  have hcomp := e.diffeomorph.contMDiff.comp (pullbackLift_holomorphic I J V f)
  have h : ContMDiff (I.prod I₁) (J.prod I₁) ω
      (fun v : TotalSpace ℂ ((f : M → N) *ᵖ V) =>
        Bundle.Pullback.lift (f : M → N) (pullbackTotalMap e f v)) := by
    apply hcomp.congr
    exact pullbackTotalMap_lift e f
  intro v
  have hv := h v
  rw [Bundle.contMDiffAt_totalSpace] at hv ⊢
  exact ⟨Bundle.contMDiffAt_proj _, hv.2⟩

end AnalyticBundleIso

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative
