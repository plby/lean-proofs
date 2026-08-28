import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cousin
import Mathlib.RingTheory.Ideal.Basic

/-!
# Actual holomorphic section ideals vanishing at infinity

The section ideal on an open set of the actual Riemann sphere consists
of its actual holomorphic functions that vanish at infinity whenever
infinity belongs to that open set. Restrictions are literal function
restrictions. The sheaf condition is proved in the companion module.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- The actual ideal of holomorphic sections vanishing at infinity. -/
def vanishingIdeal (U : Opens RiemannSphere) :
    Ideal (HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) where
  carrier := {f | ∀ h : (∞ : RiemannSphere) ∈ U, f ⟨∞, h⟩ = 0}
  zero_mem' := by
    intro h
    rfl
  add_mem' := by
    intro f g hf hg h
    change f ⟨∞, h⟩ + g ⟨∞, h⟩ = 0
    rw [hf h, hg h, add_zero]
  smul_mem' := by
    intro r f hf h
    change r ⟨∞, h⟩ * f ⟨∞, h⟩ = 0
    rw [hf h, mul_zero]

@[simp] theorem mem_vanishingIdeal (U : Opens RiemannSphere)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    f ∈ vanishingIdeal U ↔ ∀ h : (∞ : RiemannSphere) ∈ U, f ⟨∞, h⟩ = 0 := Iff.rfl

/-- These sections are literal elements of the actual vanishing ideal. -/
abbrev NegativeOneSection (U : Opens RiemannSphere) := ↥(vanishingIdeal U)

instance negativeOneSectionCoeFun (U : Opens RiemannSphere) :
    CoeFun (NegativeOneSection U) (fun _ => U → ℂ) where
  coe f := f.val

/-- Actual section evaluation is evaluation of the underlying holomorphic map. -/
@[simp] theorem negativeOneSection_apply (U : Opens RiemannSphere)
    (f : NegativeOneSection U) (x : U) : f x = f.val x := rfl

/-- Every section of the ideal vanishes at infinity on its domain. -/
theorem negativeOneSection_infty (U : Opens RiemannSphere) (f : NegativeOneSection U)
    (h : (∞ : RiemannSphere) ∈ U) : f ⟨∞, h⟩ = 0 := f.property h

/-- The pointwise complex scalar action preserves the actual section ideal. -/
instance negativeOneSectionModule (U : Opens RiemannSphere) :
    Module ℂ (NegativeOneSection U) :=
  inferInstanceAs (Module ℂ ((vanishingIdeal U).restrictScalars ℂ))

@[simp] theorem negativeOneSection_smul_val (U : Opens RiemannSphere)
    (c : ℂ) (f : NegativeOneSection U) :
    (c • f).val = c • f.val := rfl

/-- Restriction of actual vanishing sections, as an additive homomorphism. -/
def negativeOneRestriction {U V : Opens RiemannSphere} (h : U ≤ V) :
    NegativeOneSection V →+ NegativeOneSection U where
  toFun f :=
    ⟨ContMDiffMap.restrictRingHom 𝓘(ℂ) 𝓘(ℂ) ℂ h f.val,
      fun hinfty => f.property (h hinfty)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem negativeOneRestriction_val {U V : Opens RiemannSphere} (h : U ≤ V)
    (f : NegativeOneSection V) :
    (negativeOneRestriction h f).val =
      ContMDiffMap.restrictRingHom 𝓘(ℂ) 𝓘(ℂ) ℂ h f.val := rfl

@[simp] theorem negativeOneRestriction_apply {U V : Opens RiemannSphere} (h : U ≤ V)
    (f : NegativeOneSection V) (x : U) :
    negativeOneRestriction h f x = f ⟨x, h x.property⟩ := rfl

/-- The actual restrictions are also complex-linear. -/
def negativeOneRestrictionLinearMap {U V : Opens RiemannSphere} (h : U ≤ V) :
    NegativeOneSection V →ₗ[ℂ] NegativeOneSection U where
  __ := negativeOneRestriction h
  map_smul' _ _ := rfl

/-- The presheaf of actual holomorphic functions vanishing at infinity. -/
def negativeOnePresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of RiemannSphere) where
  obj U := AddCommGrpCat.of (NegativeOneSection U.unop)
  map h := AddCommGrpCat.ofHom (negativeOneRestriction (leOfHom h.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

theorem negativeOnePresheaf_obj_eq (U : Opens RiemannSphere) :
    negativeOnePresheaf.obj (op U) = AddCommGrpCat.of (NegativeOneSection U) := rfl

/-- The object modules are the literal pointwise complex modules on the ideals. -/
instance negativeOnePresheaf_obj_module (U : (Opens (TopCat.of RiemannSphere))ᵒᵖ) :
    Module ℂ (negativeOnePresheaf.obj U) :=
  negativeOneSectionModule U.unop

@[simp] theorem negativeOnePresheaf_map_apply {U V : Opens RiemannSphere} (h : U ≤ V)
    (f : NegativeOneSection V) :
    negativeOnePresheaf.map (homOfLE h).op f = negativeOneRestriction h f := rfl

/-- The actual inclusion into the additive holomorphic-function presheaf. -/
def negativeOnePresheafInclusion : negativeOnePresheaf ⟶ sphereSheaf.obj where
  app _U := AddCommGrpCat.ofHom
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

@[simp] theorem negativeOnePresheafInclusion_apply (U : Opens RiemannSphere)
    (f : NegativeOneSection U) :
    negativeOnePresheafInclusion.app (op U) f = f.val := rfl

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
