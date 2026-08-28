import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeProjection
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardLocalIsoLinear

/-!
# O-linear genuine relative canonical projection formula

The actual sheaf restrictions are semilinear over the literal restriction
of holomorphic functions. The proved local projection-formula comparisons
are O-linear, so their genuine glued global section isomorphism is O-linear
on every original open. The underlying maps are the already constructed
actual sheaf maps, not replacement module structures.
-/

noncomputable section

open TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative

open HolomorphicFunctionSheaf.SphereH1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

instance directImage_obj_baseModule (U : Opens RiemannSphere) :
    Module (Threefold.BaseSection U) (directImage.obj.obj (op U)) :=
  inferInstanceAs (Module (Threefold.BaseSection U) (Section U))

instance baseTensorSheaf_obj_baseModule (U : Opens RiemannSphere) :
    Module (Threefold.BaseSection U) (baseTensorSheaf.obj.obj (op U)) :=
  inferInstanceAs (Module (Threefold.BaseSection U) (BaseTensorSection U))

/-- The genuine projection-formula section equivalence is linear over
the actual ring of holomorphic functions on every original base open. -/
def projectionFormulaSectionLinearEquiv (U : Opens RiemannSphere) :
    Section U ≃ₗ[Threefold.BaseSection U] BaseTensorSection U := by
  letI : ∀ b : Bool, Module (Threefold.BaseSection (U ⊓ NegativeOneFrames.frameChart b))
      (CanonicalPushforwardLocalIso.Section directImage
        (CanonicalPushforwardLocalIso.chartCover NegativeOneFrames.frameChart U b)) :=
    fun b => directImage_obj_baseModule (U ⊓ NegativeOneFrames.frameChart b)
  letI : ∀ b : Bool, Module (Threefold.BaseSection (U ⊓ NegativeOneFrames.frameChart b))
      (CanonicalPushforwardLocalIso.Section baseTensorSheaf
        (CanonicalPushforwardLocalIso.chartCover NegativeOneFrames.frameChart U b)) :=
    fun b => baseTensorSheaf_obj_baseModule (U ⊓ NegativeOneFrames.frameChart b)
  exact projectionFormulaData.sectionLinearEquiv U (Threefold.BaseSection U)
    (fun b => Threefold.BaseSection (U ⊓ NegativeOneFrames.frameChart b))
    (fun _ => (HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere
      inf_le_left).toRingHom)
    (by
      intro b f s
      apply NativeBundleSections.Section.ext RelativeBundle.bundle IF
      intro x
      rfl)
    (by
      intro b f s
      apply NativeBundleSections.Section.ext baseTensorData.core 𝓘(ℂ)
      intro p
      rfl)
    (by
      intro b f s
      exact (localLinearEquiv b (U ⊓ NegativeOneFrames.frameChart b)
        inf_le_right).map_smul f s)

@[simp] theorem projectionFormulaSectionLinearEquiv_apply (U : Opens RiemannSphere)
    (s : Section U) :
    projectionFormulaSectionLinearEquiv U s = projectionFormulaSectionAddEquiv U s := rfl

@[simp] theorem projectionFormulaSectionLinearEquiv_symm_apply (U : Opens RiemannSphere)
    (s : BaseTensorSection U) :
    (projectionFormulaSectionLinearEquiv U).symm s =
      (projectionFormulaSectionAddEquiv U).symm s := rfl

/-- The actual categorical map preserves the actual holomorphic base scalar action. -/
theorem projectionFormulaSheafIso_hom_app_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : Section U) :
    projectionFormulaSheafIso.hom.hom.app (op U) (f • s) =
      f • projectionFormulaSheafIso.hom.hom.app (op U) s :=
  (projectionFormulaSectionLinearEquiv U).map_smul f s

theorem projectionFormulaSheafIso_inv_app_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : BaseTensorSection U) :
    projectionFormulaSheafIso.inv.hom.app (op U) (f • s) =
      f • projectionFormulaSheafIso.inv.hom.app (op U) s :=
  (projectionFormulaSectionLinearEquiv U).symm.map_smul f s

theorem projectionFormulaSectionLinearEquiv_restrict {U V : Opens RiemannSphere}
    (h : U ≤ V) (s : Section V) :
    NativeBundleSections.Section.restrict baseTensorData.core 𝓘(ℂ) h
        (projectionFormulaSectionLinearEquiv V s) =
      projectionFormulaSectionLinearEquiv U
        (NativeBundleSections.Section.restrict RelativeBundle.bundle IF
          (Threefold.basePreimage_mono h) s) :=
  projectionFormulaSectionAddEquiv_restrict h s

theorem projectionFormulaSectionLinearEquiv_symm_restrict {U V : Opens RiemannSphere}
    (h : U ≤ V) (s : BaseTensorSection V) :
    NativeBundleSections.Section.restrict RelativeBundle.bundle IF
        (Threefold.basePreimage_mono h) ((projectionFormulaSectionLinearEquiv V).symm s) =
      (projectionFormulaSectionLinearEquiv U).symm
        (NativeBundleSections.Section.restrict baseTensorData.core 𝓘(ℂ) h s) :=
  projectionFormulaSectionAddEquiv_symm_restrict h s

/-- The linear equivalence retains the exact original local contraction map. -/
theorem projectionFormulaSectionLinearEquiv_eq_local (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    projectionFormulaSectionLinearEquiv U = localLinearEquiv b U hU := by
  apply LinearEquiv.ext
  intro s
  exact congrArg (fun e : Section U ≃+ BaseTensorSection U => e s)
    (projectionFormulaSectionAddEquiv_eq_local b U hU)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative
