import Wikipedia.HopfProblem.PeriodTorusExponentialChernFactor

/-!
# Original exponential and winding Chern classes of native torus line bundles

The equality for original factor bundles extends through genuine analytic
bundle isomorphisms to every original native holomorphic line bundle.
Both class definitions remain unchanged.  The original winding type and
realization theorems consequently apply to the genuine exponential class
under the canonical constant-sheaf--singular comparison.
-/

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative
open PeriodTorusLineBundleClassificationFactorDescent
open SingularCohomologyFree PeriodTorusCohomology PeriodTorusTypeOneOne

universe u

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable (p : PeriodDomain) (V : p.Torus → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

/-- Any genuine factor presentation computes the exponential Chern
class as the original native boundary-winding class of that factor. -/
theorem nativeFirstChernClass_eq_of_presentation (F : FactorOfAutomorphy p)
    (e : AnalyticBundleIso IC (Core.data F).core.Fiber V) :
    nativeFirstChernClass p V = PeriodTorusLineBundle.Chern.firstChernClass F :=
  (nativeFirstChernClass_eq_of_iso p (Core.data F).core.Fiber V e).symm.trans
    (nativeFirstChernClass_factor F)

/-- The original exponential connecting class, under the original
constant-sheaf comparison, is the independently defined native winding
Chern class of every original holomorphic line bundle. -/
theorem nativeFirstChernClass_eq_winding :
    nativeFirstChernClass p V = PeriodTorusLineBundle.ChernNative.firstChernClass p V :=
  nativeFirstChernClass_eq_of_presentation p V (nativeFactor p V) (nativeFactorBundleIso p V)

/-- This is an equality of the literal original sheaf-Chern class and
the original singular winding class under the actual comparison map. -/
theorem integralH2Comparison_nativeFirstChernClass :
    integralH2Comparison p (HolomorphicPicard.Chern.nativeFirstChernClass IC p.Torus V) =
      PeriodTorusLineBundle.ChernNative.firstChernClass p V :=
  nativeFirstChernClass_eq_winding p V

/-- The genuine exponential Chern class satisfies the actual original
complex-structure type condition, by the proved winding comparison. -/
theorem nativeFirstChernClass_isTypeOneOne :
    IsTypeOneOne (cohomologyRealForm p (nativeFirstChernClass p V)) := by
  rw [nativeFirstChernClass_eq_winding]
  exact PeriodTorusLineBundle.ChernNative.firstChernClass_isTypeOneOne p V

/-- The actual image of native exponential Chern classes is exactly
the original integral type-`(1,1)` locus; realization uses genuine native
holomorphic bundles from the original factor construction. -/
theorem exists_native_firstChernClass_iff_typeOneOne (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    (∃ V : PeriodTorusLineBundle.ChernNative.NativeLineBundle.{0} p,
      nativeFirstChernClass p V.Fiber = a) ↔
      IsTypeOneOne (cohomologyRealForm p a) := by
  constructor
  · rintro ⟨V, rfl⟩
    exact nativeFirstChernClass_isTypeOneOne p V.Fiber
  · intro ha
    obtain ⟨V, hV⟩ :=
      (PeriodTorusLineBundle.ChernNative.exists_native_isFirstChernClass_iff_typeOneOne p a).mpr ha
    refine ⟨V, (nativeFirstChernClass_eq_winding p V.Fiber).trans ?_⟩
    exact ((PeriodTorusLineBundle.ChernNative.isFirstChernClass_iff p V.Fiber a).mp hV).symm

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
