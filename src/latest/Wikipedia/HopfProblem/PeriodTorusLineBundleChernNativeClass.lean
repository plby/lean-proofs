import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativeTypeOneOne
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentNative

/-!
# The genuine first Chern class of every native holomorphic line bundle

The analytic descent theorem constructs a factor presentation of any
original native holomorphic line bundle. Its winding-defined singular
class is independent of the actual presentation, by the proved native
bundle-isomorphism invariance. Thus the definition applies to all native
line bundles without a frame, factor, or classification hypothesis.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative
open PeriodTorusLineBundleClassificationFactorDescent
open SingularCohomologyFree PeriodTorusCohomology PeriodTorusTypeOneOne

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

/-- The first Chern class obtained from actual native boundary-section winding
after the proved analytic factor descent. -/
def firstChernClass : SingularCohomology p.Torus 2 :=
  Chern.firstChernClass (nativeFactor p V)

/-- The definition is the actual winding class of a genuine presentation of the original bundle. -/
theorem isFirstChernClass : IsFirstChernClass V (firstChernClass p V) :=
  ⟨nativeFactor p V, ⟨nativeFactorBundleIso p V⟩, rfl⟩

/-- Every original native holomorphic line bundle has exactly one such class. -/
theorem existsUnique_firstChernClass :
    ∃! a : SingularCohomology p.Torus 2, IsFirstChernClass V a :=
  ⟨firstChernClass p V, isFirstChernClass p V,
    fun _ ha => ha.unique (isFirstChernClass p V)⟩

theorem isFirstChernClass_iff (a : SingularCohomology p.Torus 2) :
    IsFirstChernClass V a ↔ a = firstChernClass p V := by
  constructor
  · exact fun ha => ha.unique (isFirstChernClass p V)
  · rintro rfl
    exact isFirstChernClass p V

/-- Any actual analytic presentation computes the same native first Chern class. -/
theorem firstChernClass_eq_of_presentation (F : FactorOfAutomorphy p)
    (e : AnalyticBundleIso IC (Core.data F).core.Fiber V) :
    firstChernClass p V = Chern.firstChernClass F :=
  firstChernClass_eq_of_presentations (nativeFactorBundleIso p V) e

/-- The native class has the actual complex-structure type condition, without an AH hypothesis. -/
theorem firstChernClass_isTypeOneOne :
    IsTypeOneOne (cohomologyRealForm p (firstChernClass p V)) :=
  (isFirstChernClass p V).isTypeOneOne

/-- Isomorphic original native holomorphic bundles have equal genuine singular classes. -/
theorem firstChernClass_bundleIso (W : p.Torus → Type*)
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ W] [VectorBundle ℂ ℂ W] [ContMDiffVectorBundle ω ℂ W IC]
    (e : AnalyticBundleIso IC V W) :
    firstChernClass p V = firstChernClass p W :=
  ((isFirstChernClass p V).map e).unique (isFirstChernClass p W)

/-- For the original native factor bundle this definition recovers its actual winding class. -/
@[simp] theorem firstChernClass_factor (F : FactorOfAutomorphy p) :
    firstChernClass p (Core.data F).core.Fiber = Chern.firstChernClass F :=
  firstChernClass_eq_of_presentation p _ F (AnalyticBundleIso.refl _)

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative
