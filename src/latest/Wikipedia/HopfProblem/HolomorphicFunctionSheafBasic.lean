import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Topology.Sheaves.Forget

/-!
# The genuine sheaf of holomorphic complex-valued functions

Sections on an open set are actual bundled `ContMDiff` maps of analytic
order `ω` into `ℂ`.  Restriction is literal function restriction, and the
sheaf condition follows from mathlib's proved local-invariant-property
construction at analytic order.  This is not the smooth real-function
sheaf, and analyticity is not replaced by an unproved locality premise.

For a boundaryless complex manifold this is its holomorphic function
sheaf.  The construction itself only needs the given complex charts.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The actual holomorphic maps on an open set in the given charts. -/
abbrev Section (U : Opens M) := ContMDiffMap I 𝓘(ℂ) U ℂ ω

/-- The sheaf of actual holomorphic functions, initially as a sheaf of types. -/
def typeSheaf : TopCat.Sheaf (Type) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp (I := I) (I' := 𝓘(ℂ)) ω).sheaf M ℂ

/-- Sections are definitionally bundled analytic-order manifold maps. -/
theorem typeSheaf_obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (typeSheaf I M).presheaf.obj U = Section I M U.unop := rfl

/-- The ring presheaf has the actual pointwise ring operations and
literal restriction maps. -/
def presheaf : TopCat.Presheaf CommRingCat (TopCat.of M) where
  obj U := CommRingCat.of (Section I M U.unop)
  map h := CommRingCat.ofHom <|
    ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ (CategoryTheory.leOfHom h.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

instance presheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((presheaf I M).obj U) (fun _ => U.unop → ℂ) where
  coe f := f.1

/-- The actual ring-valued holomorphic function sheaf. -/
def sheaf : TopCat.Sheaf CommRingCat (TopCat.of M) where
  obj := presheaf I M
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (typeSheaf I M).property

instance sheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((sheaf I M).presheaf.obj U) (fun _ => U.unop → ℂ) where
  coe f := f.1

theorem sheaf_obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (sheaf I M).presheaf.obj U = CommRingCat.of (Section I M U.unop) := rfl

/-- Forgetting the actual ring operations recovers exactly the
local-invariant-property sheaf of holomorphic maps. -/
theorem forget_sheaf :
    (CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat)).obj (sheaf I M) =
      typeSheaf I M := rfl

@[simp] theorem restriction_apply {U V : Opens M} (h : U ≤ V)
    (f : Section I M V) (x : U) :
    (presheaf I M).map (homOfLE h).op f x = f ⟨x, h x.property⟩ := rfl

/-- The natural scalar action on every section ring is pointwise scalar
multiplication by complex constants. -/
instance section_algebra (U : (Opens (TopCat.of M))ᵒᵖ) :
    Algebra ℂ ((sheaf I M).presheaf.obj U) :=
  inferInstanceAs (Algebra ℂ (Section I M U.unop))

@[simp] theorem algebraMap_apply (U : Opens M) (c : ℂ) (x : U) :
    algebraMap ℂ ((sheaf I M).presheaf.obj (op U)) c x = c := rfl

/-- Each actual restriction is also a homomorphism of complex algebras. -/
def restrictionAlgHom {U V : Opens M} (h : U ≤ V) :
    Section I M V →ₐ[ℂ] Section I M U where
  __ := ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ h
  commutes' _ := rfl

@[simp] theorem restrictionAlgHom_apply {U V : Opens M} (h : U ≤ V)
    (f : Section I M V) (x : U) :
    restrictionAlgHom I M h f x = f ⟨x, h x.property⟩ := rfl

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
