import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentFrame
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame

/-!
# Factor presentation of an arbitrary native holomorphic line bundle

The preceding native holomorphic-frame construction supplies the section
on the actual universal-cover pullback. Applying the proved descent gives
a genuine factor and a native analytic fibre-linear isomorphism. No frame,
pullback triviality, or factor presentation is assumed in this endpoint.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative
open PeriodTorusLineBundleClassificationHolomorphicFrame

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

/-- A factor constructed for an arbitrary original native holomorphic line bundle. -/
def nativeFactor : FactorOfAutomorphy p :=
  frameFactor (pullbackHolomorphicSection p V) (pullbackHolomorphicSection_ne_zero p V)

/-- The original native bundle is analytically the actual factor bundle,
with its original topology, atlas, and fibrewise complex-linear structure. -/
def nativeFactorBundleIso : AnalyticBundleIso IC (Core.data (nativeFactor p V)).core.Fiber V :=
  frameFactorBundleIso (pullbackHolomorphicSection p V)
    (pullbackHolomorphicSection_ne_zero p V)

/-- Every actual native holomorphic complex line bundle on the period torus
has a factor presentation. The only hypotheses are its native bundle classes. -/
theorem exists_native_factor_presentation :
    ∃ F : FactorOfAutomorphy p,
      Nonempty (AnalyticBundleIso IC (Core.data F).core.Fiber V) :=
  ⟨nativeFactor p V, ⟨nativeFactorBundleIso p V⟩⟩

/-- On actual orbit representatives the map is the constructed native
holomorphic frame multiplied by the original scalar coordinate. -/
theorem nativeFactorBundleIso_associatedMap (z : ComplexPlane₂) (c : ℂ) :
    (nativeFactorBundleIso p V).diffeomorph
      (Core.fromAssociated (nativeFactor p V) (associatedMap (nativeFactor p V) (z, c))) =
      coverScalarMap (pullbackHolomorphicSection p V) (z, c) :=
  frameFactorBundleIso_associatedMap (pullbackHolomorphicSection p V)
    (pullbackHolomorphicSection_ne_zero p V) z c

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent
