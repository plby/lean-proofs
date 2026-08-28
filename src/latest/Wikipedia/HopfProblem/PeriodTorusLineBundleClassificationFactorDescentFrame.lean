import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentFactor
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentIdentification

/-!
# Factor presentation from an actual nowhere-zero holomorphic frame

The factor and its equivariance are derived from the frame. Thus this
specialization assumes no factor data and no descended isomorphism: both
are constructed from the given native section.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable {p : PeriodDomain} {V : p.Torus → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

variable (s : CoverSection p V) (hne : ∀ z, s z ≠ 0)

/-- The actual native bundle isomorphism for the factor derived from the
given section. Equivariance and both analytic directions are proved. -/
def frameFactorBundleIso :
    AnalyticBundleIso IC (Core.data (frameFactor s hne)).core.Fiber V :=
  frameDescentIso s hne (frameFactor s hne) (frameFactor_equivariance s hne)

theorem frameFactorBundleIso_associatedMap (z : ComplexPlane₂) (c : ℂ) :
    (frameFactorBundleIso s hne).diffeomorph
      (Core.fromAssociated (frameFactor s hne) (associatedMap (frameFactor s hne) (z, c))) =
      coverScalarMap s (z, c) :=
  frameDescentIso_associatedMap s hne (frameFactor s hne)
    (frameFactor_equivariance s hne) z c

include s hne in
theorem exists_factor_presentation_of_nonzero_section :
    ∃ F : FactorOfAutomorphy p,
      Nonempty (AnalyticBundleIso IC (Core.data F).core.Fiber V) :=
  ⟨frameFactor s hne, ⟨frameFactorBundleIso s hne⟩⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent
