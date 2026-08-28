import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeBundleIntrinsic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionComparisonNative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardBaseIdeal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSheaf
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardTensorLocal

/-!
# Original section sheaves for relative canonical projection

The relative canonical section sheaf uses the genuine tensor bundle
whose fibres are full three-covectors tensor the dual sphere cotangent
line. Its direct image is the actual sheaf pushforward. On the absolute
factor, the already proved native canonical descent identifies the true
Jacobian-presentation sections with sections of the original base ideal
bundle on every open, linearly over holomorphic base functions.
-/

noncomputable section

open Bundle Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative

open HolomorphicFunctionSheaf.SphereH1
open CanonicalGlobalLineBundle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Native relative canonical sections on the full original preimage. -/
abbrev Section (U : Opens RiemannSphere) :=
  NativeBundleSections.Section RelativeBundle.bundle IF (Threefold.basePreimage U)

/-- The actual native relative canonical sheaf on the original threefold. -/
def canonicalSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of Threefold.Space) :=
  NativeBundleSections.sheaf RelativeBundle.bundle IF

/-- Mathlib's actual direct image of the native relative canonical sheaf. -/
def directImage : TopCat.Sheaf AddCommGrpCat (TopCat.of RiemannSphere) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat Threefold.sphereProjectionMap).obj canonicalSheaf

theorem directImage_obj_eq (U : Opens RiemannSphere) :
    directImage.obj.obj (op U) = AddCommGrpCat.of (Section U) := rfl

/-- Base holomorphic functions act by actual pullback in the original tensor fibres. -/
instance sectionBaseModule (U : Opens RiemannSphere) :
    Module (Threefold.BaseSection U) (Section U) :=
  Module.compHom (Section U) (Threefold.pullbackSection U).toRingHom

@[simp] theorem section_base_smul_apply (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : Section U) (x : Threefold.basePreimage U) :
    (f • s) x = f (Threefold.baseProjection U x) • s x := rfl

/-- The same actual base action on the genuine native Jacobian presentation. -/
instance presentationBaseModule (U : Opens RiemannSphere) :
    Module (Threefold.BaseSection U) (PresentationSection (Threefold.basePreimage U)) :=
  Module.compHom (PresentationSection (Threefold.basePreimage U))
    (Threefold.pullbackSection U).toRingHom

@[simp] theorem presentation_base_smul_apply (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : PresentationSection (Threefold.basePreimage U))
    (x : Threefold.basePreimage U) :
    (f • s) x = f (Threefold.baseProjection U x) • s x := rfl

/-- The actual candidate base tensor bundle for the projection formula. -/
def baseTensorData : HolomorphicCharacterBundle.TransitionData RiemannSphere (Bool × Bool) :=
  tensor CanonicalGlobal.BaseTwist.data RelativeBundle.baseData

instance baseTensorData_isHolomorphic : baseTensorData.IsHolomorphic 𝓘(ℂ) :=
  tensor_isHolomorphic CanonicalGlobal.BaseTwist.data RelativeBundle.baseData 𝓘(ℂ)

abbrev BaseTensorSection (U : Opens RiemannSphere) :=
  NativeBundleSections.Section baseTensorData.core 𝓘(ℂ) U

/-- The actual native sheaf of the base tensor line, before cancellation. -/
def baseTensorSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of RiemannSphere) :=
  NativeBundleSections.sheaf baseTensorData.core 𝓘(ℂ)

theorem baseTensorSheaf_obj_eq (U : Opens RiemannSphere) :
    baseTensorSheaf.obj.obj (op U) = AddCommGrpCat.of (BaseTensorSection U) := rfl

/-- Native presentation sections descend through the original canonical
bundle isomorphism and the proved absolute canonical direct image. -/
def presentationToIdealLinearEquiv (U : Opens RiemannSphere) :
    PresentationSection (Threefold.basePreimage U) ≃ₗ[Threefold.BaseSection U]
      NegativeOneSection U where
  toFun s := canonicalSectionIdealEquiv U
    ((nativePresentationSectionLinearEquiv (Threefold.basePreimage U)).symm s)
  invFun h := nativePresentationSectionLinearEquiv (Threefold.basePreimage U)
    ((canonicalSectionIdealEquiv U).symm h)
  left_inv s := by
    dsimp only
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  right_inv h := by
    dsimp only
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  map_add' s t := by rw [map_add, map_add]
  map_smul' f s := by
    change canonicalSectionIdealEquiv U
        ((nativePresentationSectionLinearEquiv (Threefold.basePreimage U)).symm
          (Threefold.pullbackSection U f • s)) = _
    rw [nativePresentationSectionLinearEquiv_symm_base_smul, map_smul]
    rfl

/-- The absolute factor is identified with actual native sections of
the base ideal bundle, not with a newly assigned scalar line. -/
def presentationToBaseLinearEquiv (U : Opens RiemannSphere) :
    PresentationSection (Threefold.basePreimage U) ≃ₗ[Threefold.BaseSection U]
      BaseIdeal.BundleSection U :=
  (presentationToIdealLinearEquiv U).trans (BaseIdeal.sectionLinearEquiv U).symm

@[simp] theorem presentationToBaseLinearEquiv_apply (U : Opens RiemannSphere)
    (s : PresentationSection (Threefold.basePreimage U)) :
    presentationToBaseLinearEquiv U s = (BaseIdeal.sectionLinearEquiv U).symm
      (canonicalSectionIdealEquiv U
        ((nativePresentationSectionLinearEquiv (Threefold.basePreimage U)).symm s)) := rfl

/-- The native absolute-factor comparison respects every actual restriction. -/
theorem presentationToIdealLinearEquiv_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PresentationSection (Threefold.basePreimage V)) :
    presentationToIdealLinearEquiv U
        (NativeBundleSections.Section.restrict NativePresentation.transitionBundle IF
          (Threefold.basePreimage_mono h) s) =
      negativeOneRestriction h (presentationToIdealLinearEquiv V s) := by
  change canonicalSectionIdealEquiv U
      ((nativePresentationSectionLinearEquiv (Threefold.basePreimage U)).symm
        (NativeBundleSections.Section.restrict NativePresentation.transitionBundle IF
          (Threefold.basePreimage_mono h) s)) = _
  rw [nativePresentationSectionLinearEquiv_symm_restrict]
  exact canonicalSectionIdealEquiv_restrict h _

theorem presentationToBaseLinearEquiv_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PresentationSection (Threefold.basePreimage V)) :
    presentationToBaseLinearEquiv U
        (NativeBundleSections.Section.restrict NativePresentation.transitionBundle IF
          (Threefold.basePreimage_mono h) s) =
      BaseIdeal.bundleRestrict h (presentationToBaseLinearEquiv V s) := by
  change (BaseIdeal.sectionLinearEquiv U).symm
      (presentationToIdealLinearEquiv U
        (NativeBundleSections.Section.restrict NativePresentation.transitionBundle IF
          (Threefold.basePreimage_mono h) s)) = _
  rw [presentationToIdealLinearEquiv_restrict, BaseIdeal.sectionLinearEquiv_symm_restrict]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative
