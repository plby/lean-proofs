import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativeBundlesBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernFactorTypeOneOne

/-!
# Native Chern-class type and actual bundle realization

The winding class attached through any actual native presentation is of
type `(1,1)`. Conversely every integral native class of that type is the
winding class of an explicitly constructed original native line bundle.
The existence of a presentation for an arbitrary given native bundle is
a separate analytic theorem, not a hypothesis hidden in the wrapper.
-/

noncomputable section

open Bundle

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative

open SingularCohomologyFree PeriodTorusCohomology PeriodTorusTypeOneOne
open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

variable {p : PeriodDomain} {V : p.Torus → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V]

/-- Any genuine native presentation gives the actual complex-structure type condition. -/
theorem IsFirstChernClass.isTypeOneOne {a : SingularCohomology p.Torus 2}
    (ha : IsFirstChernClass V a) : IsTypeOneOne (cohomologyRealForm p a) := by
  obtain ⟨F, _, rfl⟩ := ha
  exact Chern.firstChernClass_isTypeOneOne F

/-- Realization is by actual native holomorphic line bundles, not assigned cohomology data. -/
theorem exists_native_isFirstChernClass_iff_typeOneOne (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    (∃ V : NativeLineBundle.{0} p, IsFirstChernClass V.Fiber a) ↔
      IsTypeOneOne (cohomologyRealForm p a) := by
  constructor
  · rintro ⟨V, hV⟩
    exact hV.isTypeOneOne
  · intro ha
    obtain ⟨F, hF⟩ := (Chern.exists_factor_firstChernClass_iff_typeOneOne p a).mpr ha
    exact ⟨NativeLineBundle.ofFactor p F, F, ⟨AnalyticBundleIso.refl _⟩, hF⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative
