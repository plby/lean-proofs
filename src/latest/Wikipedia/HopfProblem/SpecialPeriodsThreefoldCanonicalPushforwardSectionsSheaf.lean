import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsLinear
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsGluing
import Mathlib.Algebra.Category.Grp.Limits

/-!
# The genuine sheaf of holomorphic native bundle sections

The objects are the actual holomorphic sections valued in the original
bundle fibres, with their pointwise additive and scalar operations.
The presheaf maps are literal restrictions. Its sheaf condition follows
from the proved unique gluing of native total-space section maps.
-/

noncomputable section

open Bundle Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.NativeBundleSections

variable {M : Type} {ι : Type*} [TopologicalSpace M]
  (C : VectorBundleCore ℂ M ℂ ι)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
  [C.IsContMDiff I ω]

/-- The additive presheaf of actual holomorphic sections of the original
native line bundle, with literal restriction maps. -/
def presheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of M) where
  obj U := AddCommGrpCat.of (Section C I U.unop)
  map h := AddCommGrpCat.ofHom (Section.restrictionAddHom C I (leOfHom h.unop))
  map_id _ := by
    ext s x
    rfl
  map_comp _ _ := by
    ext s x
    rfl

theorem presheaf_obj_eq (U : Opens M) :
    (presheaf C I).obj (op U) = AddCommGrpCat.of (Section C I U) := rfl

instance presheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((presheaf C I).obj U) (fun _ => ∀ x : U.unop, C.Fiber (x : M)) where
  coe s := s.toFun

/-- The complex module on each presheaf object is the actual pointwise
module on the original fibres. -/
instance presheaf_obj_complexModule (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module ℂ ((presheaf C I).obj U) :=
  inferInstanceAs (Module ℂ (Section C I U.unop))

/-- Holomorphic functions act on the original section values pointwise. -/
instance presheaf_obj_holomorphicModule (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module (HolomorphicFunctionSheaf.Section I M U.unop) ((presheaf C I).obj U) :=
  inferInstanceAs (Module (HolomorphicFunctionSheaf.Section I M U.unop)
    (Section C I U.unop))

@[simp] theorem presheaf_map_eq_restrict {U V : Opens M} (h : U ≤ V)
    (s : Section C I V) :
    (presheaf C I).map (homOfLE h).op s = Section.restrict C I h s := rfl

@[simp] theorem presheaf_map_apply {U V : Opens M} (h : U ≤ V)
    (s : Section C I V) (x : U) :
    (presheaf C I).map (homOfLE h).op s x = s ⟨(x : M), h x.property⟩ := rfl

/-- Unique gluing is proved for actual sections, so the additive
presheaf satisfies the categorical sheaf condition unconditionally. -/
theorem presheaf_isSheaf : (presheaf C I).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (presheaf C I)).mpr
  intro κ U s hs
  exact Section.existsUnique_gluing C I U s hs

/-- The genuine additive sheaf of actual holomorphic sections of the
original native line bundle. -/
def sheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of M) where
  obj := presheaf C I
  property := presheaf_isSheaf C I

theorem sheaf_obj_eq (U : Opens M) :
    (sheaf C I).obj.obj (op U) = AddCommGrpCat.of (Section C I U) := rfl

instance sheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((sheaf C I).obj.obj U) (fun _ => ∀ x : U.unop, C.Fiber (x : M)) where
  coe s := s.toFun

instance sheaf_obj_complexModule (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module ℂ ((sheaf C I).obj.obj U) :=
  inferInstanceAs (Module ℂ (Section C I U.unop))

instance sheaf_obj_holomorphicModule (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module (HolomorphicFunctionSheaf.Section I M U.unop) ((sheaf C I).obj.obj U) :=
  inferInstanceAs (Module (HolomorphicFunctionSheaf.Section I M U.unop)
    (Section C I U.unop))

/-- The complex-linear identification with native sections is literally
the identity, with no change of fibres or scalar action. -/
def sectionLinearEquiv (U : Opens M) :
    (sheaf C I).obj.obj (op U) ≃ₗ[ℂ] Section C I U :=
  LinearEquiv.refl ℂ _

@[simp] theorem sectionLinearEquiv_apply (U : Opens M)
    (s : (sheaf C I).obj.obj (op U)) : sectionLinearEquiv C I U s = s := rfl

@[simp] theorem sheaf_map_eq_restrict {U V : Opens M} (h : U ≤ V)
    (s : Section C I V) :
    (sheaf C I).obj.map (homOfLE h).op s = Section.restrict C I h s := rfl

@[simp] theorem sheaf_map_apply {U V : Opens M} (h : U ≤ V)
    (s : Section C I V) (x : U) :
    (sheaf C I).obj.map (homOfLE h).op s x = s ⟨(x : M), h x.property⟩ := rfl

end Wikipedia.HopfProblem.NativeBundleSections
