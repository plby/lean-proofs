import Wikipedia.HopfProblem.HolomorphicPicardChern
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteCoefficients
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLocalContractibilityManifold
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativeClass

/-!
# The original exponential Chern map on the original period torus

This is the already constructed native unit-cocycle class followed by
the original exponential connecting homomorphism and the canonical
constant-sheaf--singular comparison.  The original torus supplies its own
compactness, Hausdorffness, and locally contractible native atlas.

No equality with the independently defined winding class is built into
the definition.  That equality requires a genuine representative and
connecting-map comparison.
-/

noncomputable section

open Bundle CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open HolomorphicExponentialSheaf HolomorphicPicardNative SingularCohomologyFree
  PeriodTorusLineBundleClassificationNative

universe u v

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The original torus atlas provides genuine local contractibility. -/
theorem torusLocallyContractible (p : PeriodDomain) : LocallyContractibleSpace p.Torus :=
  ConstantSheafSingularComparison.LocalContractibility.normedChartedSpace_locallyContractibleSpace
    ComplexPlane₂ p.Torus

/-- The canonical comparison has the original integral singular group
as its literal target and the original exponential integer sheaf as source. -/
def integralH2Comparison (p : PeriodDomain) :
    CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of p.Torus)) 2 ≃+
      SingularCohomology p.Torus 2 :=
  ConstantSheafSingularComparison.integralSheafH2Equiv (TopCat.of p.Torus)
    (torusLocallyContractible p)

/-- This map is exactly the frozen constant-sheaf--singular comparison. -/
theorem integralH2Comparison_eq (p : PeriodDomain) :
    integralH2Comparison p =
      ConstantSheafSingularComparison.integralSheafH2Equiv (TopCat.of p.Torus)
        (torusLocallyContractible p) := rfl

variable (p : PeriodDomain) (V : p.Torus → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

/-- The original exponential Chern class followed by the actual singular comparison. -/
def nativeFirstChernClass : SingularCohomology p.Torus 2 :=
  integralH2Comparison p (HolomorphicPicard.Chern.nativeFirstChernClass IC p.Torus V)

/-- The literal native unit cocycle and original normalized exponential extension. -/
theorem nativeFirstChernClass_eq_cocycle :
    nativeFirstChernClass p V = integralH2Comparison p
      ((HolomorphicPicard.CechExtension.classOf (nativeCocycle IC p.Torus V)
        (nativeCover_covers p.Torus V)).comp
          (exponentialComplex_shortExact IC p.Torus).extClass rfl) := rfl

/-- Genuine native analytic fibre-linear isomorphisms preserve this class. -/
theorem nativeFirstChernClass_eq_of_iso (W : p.Torus → Type v)
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ W] [VectorBundle ℂ ℂ W] [ContMDiffVectorBundle ω ℂ W IC]
    (e : AnalyticBundleIso IC V W) :
    nativeFirstChernClass p V = nativeFirstChernClass p W :=
  congrArg (integralH2Comparison p)
    (HolomorphicPicard.Chern.nativeFirstChernClass_eq_of_iso IC p.Torus V W e)

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
