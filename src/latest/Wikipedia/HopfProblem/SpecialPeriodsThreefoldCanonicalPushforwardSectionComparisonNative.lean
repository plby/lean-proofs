import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionComparisonSheaf
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsSheafNative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalNativeCanonicalSpecial

/-!
# Actual canonical sections in the native transition presentation

The actual canonical total-space biholomorphism induces an equivalence
on every original open-set section space. It preserves each full
intrinsic alternating three-covector, commutes with restrictions, and
induces actual sheaf and direct-image isomorphisms.
-/

noncomputable section

open Bundle TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward

open TrianglePeriodFamily.Canonical

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

/-- Sections of the independently built native reverse-Jacobian bundle. -/
abbrev PresentationSection (V : Opens Threefold.Space) :=
  NativeBundleSections.Section NativePresentation.transitionBundle IF V

/-- Actual original canonical sections are identified over every open
with sections of their native unit-valued Jacobian presentation. -/
def nativePresentationSectionLinearEquiv (V : Opens Threefold.Space) :
    Section V ≃ₗ[HolomorphicFunctionSheaf.Section IF Threefold.Space V]
      PresentationSection V :=
  NativeBundleSections.Comparison.sectionLinearEquiv Threefold.Canonical.bundle
    NativePresentation.transitionBundle IF NativePresentation.bundleBiholomorph
    NativePresentation.fiberEquiv NativePresentation.bundleBiholomorph_mk V

@[simp] theorem nativePresentationSectionLinearEquiv_apply (V : Opens Threefold.Space)
    (s : Section V) (x : V) :
    nativePresentationSectionLinearEquiv V s x =
      NativePresentation.fiberEquiv (x : Threefold.Space) (s x) := rfl

@[simp] theorem nativePresentationSectionLinearEquiv_symm_apply (V : Opens Threefold.Space)
    (s : PresentationSection V) (x : V) :
    (nativePresentationSectionLinearEquiv V).symm s x =
      (NativePresentation.fiberEquiv (x : Threefold.Space)).symm (s x) := rfl

/-- No intrinsic canonical covector is changed by the section comparison. -/
theorem nativePresentationSectionLinearEquiv_intrinsic (V : Opens Threefold.Space)
    (s : Section V) (x : V) :
    NativePresentation.dataIntrinsicEquiv (x : Threefold.Space)
        (nativePresentationSectionLinearEquiv V s x) =
      Threefold.Canonical.intrinsicEquiv (x : Threefold.Space) (s x) :=
  NativePresentation.dataIntrinsicEquiv_fiberEquiv (x : Threefold.Space) (s x)

theorem nativePresentationSectionLinearEquiv_symm_intrinsic (V : Opens Threefold.Space)
    (s : PresentationSection V) (x : V) :
    Threefold.Canonical.intrinsicEquiv (x : Threefold.Space)
        ((nativePresentationSectionLinearEquiv V).symm s x) =
      NativePresentation.dataIntrinsicEquiv (x : Threefold.Space) (s x) :=
  NativePresentation.dataIntrinsicEquiv_fiberEquiv_symm (x : Threefold.Space) (s x)

theorem nativePresentationSectionLinearEquiv_restrict {V W : Opens Threefold.Space}
    (h : V ≤ W) (s : Section W) :
    nativePresentationSectionLinearEquiv V (restrictSection h s) =
      NativeBundleSections.Section.restrict NativePresentation.transitionBundle IF h
        (nativePresentationSectionLinearEquiv W s) :=
  NativeBundleSections.Comparison.sectionLinearEquiv_restrict Threefold.Canonical.bundle
    NativePresentation.transitionBundle IF NativePresentation.bundleBiholomorph
    NativePresentation.fiberEquiv NativePresentation.bundleBiholomorph_mk h s

theorem nativePresentationSectionLinearEquiv_symm_restrict {V W : Opens Threefold.Space}
    (h : V ≤ W) (s : PresentationSection W) :
    (nativePresentationSectionLinearEquiv V).symm
        (NativeBundleSections.Section.restrict NativePresentation.transitionBundle IF h s) =
      restrictSection h ((nativePresentationSectionLinearEquiv W).symm s) :=
  NativeBundleSections.Comparison.sectionLinearEquiv_symm_restrict Threefold.Canonical.bundle
    NativePresentation.transitionBundle IF NativePresentation.bundleBiholomorph
    NativePresentation.fiberEquiv NativePresentation.bundleBiholomorph_mk h s

/-- The original base scalar action is transported through actual pullback. -/
theorem nativePresentationSectionLinearEquiv_base_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : PreimageSection U) :
    nativePresentationSectionLinearEquiv (Threefold.basePreimage U) (f • s) =
      Threefold.pullbackSection U f •
        nativePresentationSectionLinearEquiv (Threefold.basePreimage U) s :=
  (nativePresentationSectionLinearEquiv (Threefold.basePreimage U)).map_smul
    (Threefold.pullbackSection U f) s

theorem nativePresentationSectionLinearEquiv_symm_base_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : PresentationSection (Threefold.basePreimage U)) :
    (nativePresentationSectionLinearEquiv (Threefold.basePreimage U)).symm
        (Threefold.pullbackSection U f • s) =
      f • (nativePresentationSectionLinearEquiv (Threefold.basePreimage U)).symm s :=
  (nativePresentationSectionLinearEquiv (Threefold.basePreimage U)).symm.map_smul
    (Threefold.pullbackSection U f) s

/-- The actual native presentation section sheaf. -/
def presentationSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of Threefold.Space) :=
  NativeBundleSections.sheaf NativePresentation.transitionBundle IF

/-- The section comparison is an isomorphism of the genuine native sheaves. -/
def nativePresentationSheafIso : canonicalSheaf ≅ presentationSheaf :=
  NativeBundleSections.Comparison.sheafIso Threefold.Canonical.bundle
    NativePresentation.transitionBundle IF NativePresentation.bundleBiholomorph
    NativePresentation.fiberEquiv NativePresentation.bundleBiholomorph_mk

@[simp] theorem nativePresentationSheafIso_hom_app (V : Opens Threefold.Space)
    (s : Section V) :
    nativePresentationSheafIso.hom.hom.app (op V) s =
      nativePresentationSectionLinearEquiv V s := rfl

@[simp] theorem nativePresentationSheafIso_inv_app (V : Opens Threefold.Space)
    (s : PresentationSection V) :
    nativePresentationSheafIso.inv.hom.app (op V) s =
      (nativePresentationSectionLinearEquiv V).symm s := rfl

/-- Mathlib's actual direct image of the native presentation sheaf. -/
def presentationDirectImage : TopCat.Sheaf AddCommGrpCat (TopCat.of RiemannSphere) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat Threefold.sphereProjectionMap).obj presentationSheaf

/-- The native bundle comparison induces an actual direct-image isomorphism. -/
def nativePresentationDirectImageIso : canonicalDirectImage ≅ presentationDirectImage :=
  (TopCat.Sheaf.pushforward AddCommGrpCat Threefold.sphereProjectionMap).mapIso
    nativePresentationSheafIso

@[simp] theorem nativePresentationDirectImageIso_hom_app (U : Opens RiemannSphere)
    (s : PreimageSection U) :
    nativePresentationDirectImageIso.hom.hom.app (op U) s =
      nativePresentationSectionLinearEquiv (Threefold.basePreimage U) s := rfl

@[simp] theorem nativePresentationDirectImageIso_inv_app (U : Opens RiemannSphere)
    (s : PresentationSection (Threefold.basePreimage U)) :
    nativePresentationDirectImageIso.inv.hom.app (op U) s =
      (nativePresentationSectionLinearEquiv (Threefold.basePreimage U)).symm s := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward
