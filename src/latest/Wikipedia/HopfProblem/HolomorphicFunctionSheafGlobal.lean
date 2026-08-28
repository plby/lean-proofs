import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic

/-!
# Global sections are actual bundled holomorphic functions

Global sections mean sections of the constructed sheaf on the actual
top open set.  Removing that open-subset wrapper gives a complex-algebra
equivalence with the actual bundled holomorphic maps on the manifold.
Both directions and all evaluations are computed on the underlying
functions; no constancy or finite-dimensionality assumption is used.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Literal global sections of the genuine holomorphic function sheaf. -/
abbrev GlobalSections := (sheaf I M).presheaf.obj (op ⊤)

/-- The canonical map into the actual top open subset. -/
def toTopOpen (x : M) : (⊤ : Opens M) := ⟨x, trivial⟩

/-- Removing or adding the top-open wrapper is analytically harmless,
proved at analytic order rather than only at smooth order. -/
theorem toTopOpen_contMDiff : ContMDiff I I ω (toTopOpen M) := by
  intro x
  have h : ContMDiffAt I I ω (fun y : M => (toTopOpen M y : M)) x ↔
      ContMDiffAt I I ω (toTopOpen M) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp contMDiffAt_id

/-- Read an actual global sheaf section as an actual bundled holomorphic map. -/
def globalSectionToMap (f : GlobalSections I M) : ContMDiffMap I 𝓘(ℂ) M ℂ ω :=
  ⟨fun x => f (toTopOpen M x), f.contMDiff.comp (toTopOpen_contMDiff I M)⟩

/-- Regard an actual bundled holomorphic map as a section on the top open set. -/
def mapToGlobalSection (f : ContMDiffMap I 𝓘(ℂ) M ℂ ω) : GlobalSections I M :=
  ⟨fun x => f x, f.contMDiff.comp contMDiff_subtype_val⟩

@[simp] theorem globalSectionToMap_apply (f : GlobalSections I M) (x : M) :
    globalSectionToMap I M f x = f (toTopOpen M x) := rfl

@[simp] theorem mapToGlobalSection_apply (f : ContMDiffMap I 𝓘(ℂ) M ℂ ω)
    (x : (⊤ : Opens M)) : mapToGlobalSection I M f x = f x := rfl

/-- Global sections of the actual holomorphic sheaf are the actual
bundled holomorphic functions, compatibly with their complex algebras. -/
def globalSectionsAlgEquiv : GlobalSections I M ≃ₐ[ℂ] ContMDiffMap I 𝓘(ℂ) M ℂ ω where
  toFun := globalSectionToMap I M
  invFun := mapToGlobalSection I M
  left_inv f := by
    apply ContMDiffMap.ext
    intro x
    rfl
  right_inv f := by
    apply ContMDiffMap.ext
    intro x
    rfl
  map_mul' f g := by
    apply ContMDiffMap.ext
    intro x
    rfl
  map_add' f g := by
    apply ContMDiffMap.ext
    intro x
    rfl
  commutes' c := rfl

@[simp] theorem globalSectionsAlgEquiv_apply (f : GlobalSections I M) (x : M) :
    globalSectionsAlgEquiv I M f x = f (toTopOpen M x) := rfl

@[simp] theorem globalSectionsAlgEquiv_symm_apply
    (f : ContMDiffMap I 𝓘(ℂ) M ℂ ω) (x : (⊤ : Opens M)) :
    (globalSectionsAlgEquiv I M).symm f x = f x := rfl

/-- Evaluation of genuine global sheaf sections is an actual algebra homomorphism. -/
def globalSectionsEval (x : M) : GlobalSections I M →ₐ[ℂ] ℂ where
  toFun f := f (toTopOpen M x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem globalSectionsEval_apply (x : M) (f : GlobalSections I M) :
    globalSectionsEval I M x f = globalSectionsAlgEquiv I M f x := rfl

/-- Restriction of a global section is the restriction of its actual
holomorphic function to the selected open set. -/
@[simp] theorem restrict_globalSectionsAlgEquiv (U : Opens M)
    (f : GlobalSections I M) (x : U) :
    (sheaf I M).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op f x =
      globalSectionsAlgEquiv I M f x := rfl

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
