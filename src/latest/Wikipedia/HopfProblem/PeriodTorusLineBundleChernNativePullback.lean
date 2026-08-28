import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativeClass
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativePullbackIso
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback

/-!
# Genuine native Chern naturality for every holomorphic line bundle

The target bundle is arbitrary and carries only its original native
holomorphic bundle structures. Its proved factor presentation pulls back
through the genuine native pullback functor. The actual factor-pullback
calculation then gives naturality in native singular cohomology.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative
open PeriodTorusLineBundleClassificationFactorDescent
open PeriodTorusLineBundleChernPullback SingularCohomologyFree

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable {p q : PeriodDomain} (L : LatticeLinearMap p q) (V : q.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

/-- The original native pullback bundle has the actual singular pullback of its Chern class. -/
theorem firstChernClass_pullback :
    firstChernClass p ((L.torusMap : p.Torus → q.Torus) *ᵖ V) =
      singularCohomologyPullback L.torusContinuousMap 2 (firstChernClass q V) := by
  let F : FactorOfAutomorphy q := nativeFactor q V
  let e : AnalyticBundleIso IC (Core.data (pullbackFactor L F)).core.Fiber
      ((L.torusMap : p.Torus → q.Torus) *ᵖ V) :=
    (pullbackBundleIso L F).trans ((nativeFactorBundleIso q V).pullback L.torusMap)
  rw [firstChernClass_eq_of_presentation p _ (pullbackFactor L F) e,
    PeriodTorusLineBundleChernPullback.firstChernClass_pullback]
  rfl

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative
