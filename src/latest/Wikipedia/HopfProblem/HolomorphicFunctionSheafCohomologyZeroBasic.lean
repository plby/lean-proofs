import Wikipedia.HopfProblem.HolomorphicFunctionSheafGlobal
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.Algebra.Module.TransferInstance

/-!
# Actual degree-zero cohomology of the holomorphic function sheaf

The additive sheaf is obtained by forgetting the pointwise ring structure
of the actual holomorphic function sheaf. `H0` is mathlib's sheaf
cohomology, defined by `Ext`, in degree zero. The proved degree-zero
comparison identifies it with the literal global sections.

The sheafification and `Ext` infrastructure comes from the installed
instances for sheaves of abelian groups on the small open-set site; no
additional existence hypotheses are imposed here.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The actual additive sheaf underlying the holomorphic function sheaf. -/
def additiveSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of M) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj
    (sheaf I M)

/-- The additive sections retain their actual pointwise complex module. -/
instance additiveSheaf_obj_module (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module ℂ ((additiveSheaf I M).presheaf.obj U) :=
  inferInstanceAs (Module ℂ (Section I M U.unop))

/-- Genuine degree-zero sheaf cohomology, not a redefinition of global sections. -/
abbrev H0 : Type := CategoryTheory.Sheaf.H (additiveSheaf I M) 0

/-- The additive group is the existing `Ext` group structure. -/
instance h0AddCommGroup : AddCommGroup (H0 I M) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The canonical degree-zero cohomology comparison at the actual top open set. -/
def h0GlobalAddEquiv : H0 I M ≃+ GlobalSections I M :=
  CategoryTheory.Sheaf.H.equiv₀ (additiveSheaf I M)
    (show Limits.IsTerminal (⊤ : Opens (TopCat.of M)) from Limits.isTerminalTop)

/-- Complex scalar multiplication is transported along the canonical
degree-zero comparison. Its agreement with the induced maps of actual
scalar sheaf endomorphisms is proved in the scalar-action companion file. -/
instance h0Module : Module ℂ (H0 I M) :=
  (h0GlobalAddEquiv I M).module ℂ

/-- The genuine degree-zero comparison is complex linear. -/
def h0GlobalLinearEquiv : H0 I M ≃ₗ[ℂ] GlobalSections I M :=
  (h0GlobalAddEquiv I M).linearEquiv ℂ

@[simp] theorem h0GlobalLinearEquiv_apply (x : H0 I M) :
    h0GlobalLinearEquiv I M x = h0GlobalAddEquiv I M x := rfl

@[simp] theorem h0GlobalLinearEquiv_symm_apply (x : GlobalSections I M) :
    (h0GlobalLinearEquiv I M).symm x = (h0GlobalAddEquiv I M).symm x := rfl

@[simp] theorem h0GlobalAddEquiv_smul (c : ℂ) (x : H0 I M) :
    h0GlobalAddEquiv I M (c • x) = c • h0GlobalAddEquiv I M x :=
  (h0GlobalLinearEquiv I M).map_smul c x

/-- Degree-zero cohomology is complex-linearly equivalent to the actual
bundled holomorphic maps on the manifold. -/
def h0HolomorphicMapLinearEquiv : H0 I M ≃ₗ[ℂ] ContMDiffMap I 𝓘(ℂ) M ℂ ω :=
  (h0GlobalLinearEquiv I M).trans (globalSectionsAlgEquiv I M).toLinearEquiv

@[simp] theorem h0HolomorphicMapLinearEquiv_apply (x : H0 I M) :
    h0HolomorphicMapLinearEquiv I M x =
      globalSectionsAlgEquiv I M (h0GlobalAddEquiv I M x) := rfl

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
