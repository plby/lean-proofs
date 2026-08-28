import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionComparisonBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsSheaf

/-!
# Native holomorphic bundle comparisons induce genuine sheaf isomorphisms

A fibrewise-linear biholomorphism of the original native total spaces
acts on actual sections over every open set. These section equivalences
commute with literal restriction, giving an isomorphism of the genuine
additive sheaves. Both directions are linear over the actual holomorphic
functions on each open set.
-/

noncomputable section

open Bundle TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.NativeBundleSections.Comparison

variable {M : Type} {ι κ : Type*} [TopologicalSpace M]
  (C : VectorBundleCore ℂ M ℂ ι) (D : VectorBundleCore ℂ M ℂ κ)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
  [C.IsContMDiff I ω] [D.IsContMDiff I ω]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (e : Diffeomorph (I.prod I₁) (I.prod I₁) C.TotalSpace D.TotalSpace ω)
  (φ : ∀ x, C.Fiber x ≃L[ℂ] D.Fiber x)
  (he : ∀ x v, e ⟨x, v⟩ = ⟨x, φ x v⟩)

/-- The actual additive presheaf comparison, with the original native
fibre maps as its components. -/
def presheafIso : NativeBundleSections.presheaf C I ≅ NativeBundleSections.presheaf D I :=
  NatIso.ofComponents
    (fun U => (sectionLinearEquiv C D I e φ he U.unop).toAddEquiv.toAddCommGrpIso)
    (by
      intro U V h
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact sectionLinearEquiv_restrict C D I e φ he (leOfHom h.unop) s)

/-- The genuine sheaf isomorphism induced by the original native
fibrewise-linear biholomorphism. -/
def sheafIso : NativeBundleSections.sheaf C I ≅ NativeBundleSections.sheaf D I :=
  ObjectProperty.isoMk _ (presheafIso C D I e φ he)

@[simp] theorem sheafIso_hom_app (U : Opens M) (s : Section C I U) :
    (sheafIso C D I e φ he).hom.hom.app (op U) s =
      sectionLinearEquiv C D I e φ he U s := rfl

@[simp] theorem sheafIso_inv_app (U : Opens M) (s : Section D I U) :
    (sheafIso C D I e φ he).inv.hom.app (op U) s =
      (sectionLinearEquiv C D I e φ he U).symm s := rfl

/-- The sheaf comparison acts by the actual native fibre equivalence. -/
@[simp] theorem sheafIso_hom_app_apply (U : Opens M) (s : Section C I U) (x : U) :
    (sheafIso C D I e φ he).hom.hom.app (op U) s x = φ (x : M) (s x) :=
  sectionLinearEquiv_apply C D I e φ he U s x

/-- Its inverse acts by the inverse native fibre equivalence. -/
@[simp] theorem sheafIso_inv_app_apply (U : Opens M) (s : Section D I U) (x : U) :
    (sheafIso C D I e φ he).inv.hom.app (op U) s x = (φ (x : M)).symm (s x) :=
  sectionLinearEquiv_symm_apply C D I e φ he U s x

/-- Each forward component is linear over actual holomorphic functions. -/
theorem sheafIso_hom_app_smul (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section I M U) (s : Section C I U) :
    (sheafIso C D I e φ he).hom.hom.app (op U) (f • s) =
      f • id (α := Section D I U) ((sheafIso C D I e φ he).hom.hom.app (op U) s) :=
  (sectionLinearEquiv C D I e φ he U).map_smul f s

/-- Each inverse component is linear over actual holomorphic functions. -/
theorem sheafIso_inv_app_smul (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section I M U) (s : Section D I U) :
    (sheafIso C D I e φ he).inv.hom.app (op U) (f • s) =
      f • id (α := Section C I U) ((sheafIso C D I e φ he).inv.hom.app (op U) s) :=
  (sectionLinearEquiv C D I e φ he U).symm.map_smul f s

end Wikipedia.HopfProblem.NativeBundleSections.Comparison
