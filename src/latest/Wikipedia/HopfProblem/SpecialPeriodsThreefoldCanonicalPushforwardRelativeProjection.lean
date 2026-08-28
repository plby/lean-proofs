import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeLocal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardLocalIsoSheaf

/-!
# The genuine relative canonical projection formula on all base opens

The actual local tensor-contraction comparisons are natural and agree
on every common chart subopen. Genuine sheaf gluing therefore gives a
section isomorphism on every original sphere open and an isomorphism
from the actual relative canonical direct image to the actual base
tensor-bundle section sheaf. No projection formula is an input.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative

open HolomorphicFunctionSheaf.SphereH1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Every local input to gluing is the already proved actual geometric
comparison, with its compatibility proved from native tensor transitions. -/
def projectionFormulaData : CanonicalPushforwardLocalIso.Data directImage baseTensorSheaf
    NegativeOneFrames.frameChart where
  cover := NegativeOneFrames.frameChart_cover
  localEquiv b U hU := (localLinearEquiv b U hU).toAddEquiv
  naturality b _U _V h hV s := localLinearEquiv_restrict b h (h.trans hV) hV s
  agreement b c U hb hc s := localLinearEquiv_chart_independent b c U hb hc s

/-- Actual section comparison on every original sphere open. -/
def projectionFormulaSectionAddEquiv (U : Opens RiemannSphere) :
    Section U ≃+ BaseTensorSection U := projectionFormulaData.sectionAddEquiv U

/-- The global comparison retains the actual local contraction formula. -/
theorem projectionFormulaSectionAddEquiv_eq_local (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    projectionFormulaSectionAddEquiv U = (localLinearEquiv b U hU).toAddEquiv :=
  projectionFormulaData.sectionAddEquiv_eq_local b U hU

theorem projectionFormulaSectionAddEquiv_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : Section V) :
    NativeBundleSections.Section.restrict baseTensorData.core 𝓘(ℂ) h
        (projectionFormulaSectionAddEquiv V s) =
      projectionFormulaSectionAddEquiv U
        (NativeBundleSections.Section.restrict RelativeBundle.bundle IF
          (Threefold.basePreimage_mono h) s) :=
  projectionFormulaData.sectionAddEquiv_restrict h s

theorem projectionFormulaSectionAddEquiv_symm_restrict {U V : Opens RiemannSphere}
    (h : U ≤ V) (s : BaseTensorSection V) :
    NativeBundleSections.Section.restrict RelativeBundle.bundle IF
        (Threefold.basePreimage_mono h) ((projectionFormulaSectionAddEquiv V).symm s) =
      (projectionFormulaSectionAddEquiv U).symm
        (NativeBundleSections.Section.restrict baseTensorData.core 𝓘(ℂ) h s) :=
  projectionFormulaData.sectionAddEquiv_symm_restrict h s

/-- The actual sheaf projection formula for the native relative canonical
line, with the original native base tensor line on its right hand side. -/
def projectionFormulaSheafIso : directImage ≅ baseTensorSheaf :=
  projectionFormulaData.sheafIso

@[simp] theorem projectionFormulaSheafIso_hom_app (U : Opens RiemannSphere)
    (s : Section U) :
    projectionFormulaSheafIso.hom.hom.app (op U) s = projectionFormulaSectionAddEquiv U s :=
  rfl

@[simp] theorem projectionFormulaSheafIso_inv_app (U : Opens RiemannSphere)
    (s : BaseTensorSection U) :
    projectionFormulaSheafIso.inv.hom.app (op U) s =
      (projectionFormulaSectionAddEquiv U).symm s := rfl

/-- All local identities are identities of the actual sheaf map. -/
theorem projectionFormulaSheafIso_hom_app_eq_local (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : Section U) :
    projectionFormulaSheafIso.hom.hom.app (op U) s = localLinearEquiv b U hU s := by
  rw [projectionFormulaSheafIso_hom_app, projectionFormulaSectionAddEquiv_eq_local b U hU]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative
