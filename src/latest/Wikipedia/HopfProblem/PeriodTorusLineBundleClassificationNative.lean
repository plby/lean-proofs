import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIdentification
import Wikipedia.HopfProblem.PeriodTori

/-!
# Arbitrary native line bundles on the actual period tori

Every native analytic complex line bundle on the original compact period torus
has an extracted scalar transition cocycle and an actual analytic fibre-linear
identification with its cocycle bundle. The construction works for arbitrary
native bundles, not just for the factors constructed in the Appell--Humbert
realizability package.

This is the native-cocycle step of classification. It does not assert that the
pullback to `ℂ²` is holomorphically trivial or that the cocycle has an
Appell--Humbert normal form.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
    [ContMDiffVectorBundle ω ℂ V (modelWithCornersSelf ℂ ComplexPlane₂)]

/-- Scalar-cocycle realization for every actual native holomorphic complex
line bundle on the given period torus, retaining its existing analytic atlas. -/
theorem exists_scalarPresentation :
    ∃ A : HolomorphicCharacterBundle.TransitionData p.Torus p.Torus,
      A.IsHolomorphic (modelWithCornersSelf ℂ ComplexPlane₂) ∧
        Nonempty (AnalyticBundleIso (modelWithCornersSelf ℂ ComplexPlane₂) A.core.Fiber V) :=
  ⟨data V, inferInstance, ⟨identification V (modelWithCornersSelf ℂ ComplexPlane₂)⟩⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative
