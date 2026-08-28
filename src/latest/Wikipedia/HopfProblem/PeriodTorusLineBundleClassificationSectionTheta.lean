import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationSectionTransport
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreSections

/-!
# Genuine native sections and entire theta functions

An actual native bundle isomorphism transports original holomorphic
sections to the already proved theta correspondence. The covering formula
uses the actual total-space map and actual quotient representatives.
This is not a definition of meromorphic functions as section ratios.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable {p : PeriodDomain} {V : p.Torus → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V]

/-- This equivalence acts on the independently given native holomorphic sections. -/
def sectionEquivThetaOfNativeIso (F : FactorOfAutomorphy p)
    (e : AnalyticBundleIso IC (Core.data F).core.Fiber V) :
    ContMDiffSection IC ℂ ω V ≃ EntireThetaFunction F :=
  e.symm.sectionEquiv.trans (Core.sectionEquivTheta F)

theorem sectionEquivThetaOfNativeIso_symm_apply (F : FactorOfAutomorphy p)
    (e : AnalyticBundleIso IC (Core.data F).core.Fiber V)
    (θ : EntireThetaFunction F) (x : p.Torus) :
    (sectionEquivThetaOfNativeIso F e).symm θ x =
      e.fiberEquiv x ((Core.sectionEquivTheta F).symm θ x) := rfl

/-- The theta function really represents the original section on every
covering point, via the actual native analytic bundle map. -/
theorem sectionEquivThetaOfNativeIso_covering (F : FactorOfAutomorphy p)
    (e : AnalyticBundleIso IC (Core.data F).core.Fiber V)
    (s : ContMDiffSection IC ℂ ω V) (z : ComplexPlane₂) :
    e.diffeomorph (Core.fromAssociated F
      (associatedMap F (z, (sectionEquivThetaOfNativeIso F e s).val z))) =
      ⟨p.lattice.mkQ z, s (p.lattice.mkQ z)⟩ := by
  have hθ := Section.associatedMap_pullback F
    (Core.quotientSection F (e.symm.sectionEquiv s)) z
  change associatedMap F (z, (sectionEquivThetaOfNativeIso F e s).val z) =
    Core.toAssociated F ⟨p.lattice.mkQ z, (e.fiberEquiv (p.lattice.mkQ z)).symm
      (s (p.lattice.mkQ z))⟩ at hθ
  rw [hθ, Core.fromAssociated_toAssociated, e.map_fiber, LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
