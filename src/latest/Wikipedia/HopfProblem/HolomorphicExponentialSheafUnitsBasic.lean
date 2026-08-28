import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# The actual sheaf of units of holomorphic functions

The forgetful functor to commutative monoids and the units functor are right
adjoints.  Composing them with the multiplicative-to-additive equivalence
therefore preserves the genuine sheaf condition.  The resulting sections
are exactly units of the actual holomorphic section ring, written additively;
their restrictions are the original function restrictions.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Units of the actual holomorphic section ring, written as an additive group. -/
abbrev UnitSection (U : Opens M) := Additive ((HolomorphicFunctionSheaf.Section I M U)ˣ)

/-- The genuine units sheaf, obtained by functors that preserve sheaves;
no extra gluing or preservation hypothesis is imposed. -/
def unitsSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of M) :=
  (sheafCompose _ ((forget₂ CommRingCat CommMonCat) ⋙ CommMonCat.units ⋙
    commGroupAddCommGroupEquivalence.functor)).obj (HolomorphicFunctionSheaf.sheaf I M)

theorem unitsSheaf_obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (unitsSheaf I M).presheaf.obj U = AddCommGrpCat.of (UnitSection I M U.unop) :=
  rfl

variable {I M} {U : Opens M}

/-- The actual holomorphic function underlying a unit section. -/
def unitSectionVal (u : UnitSection I M U) : HolomorphicFunctionSheaf.Section I M U :=
  u.toMul.val

/-- Pointwise evaluation of the underlying holomorphic function. -/
def unitSectionEval (u : UnitSection I M U) (x : U) : ℂ := unitSectionVal u x

@[ext]
theorem unitSection_ext {u v : UnitSection I M U}
    (h : ∀ x, unitSectionEval u x = unitSectionEval v x) : u = v := by
  apply Additive.toMul.injective
  apply Units.ext
  apply ContMDiffMap.ext
  exact h

@[simp]
theorem unitSectionVal_zero : unitSectionVal (0 : UnitSection I M U) = 1 := rfl

@[simp]
theorem unitSectionEval_zero (x : U) : unitSectionEval (0 : UnitSection I M U) x = 1 := rfl

@[simp]
theorem unitSectionVal_add (u v : UnitSection I M U) :
    unitSectionVal (u + v) = unitSectionVal u * unitSectionVal v := rfl

@[simp]
theorem unitSectionEval_add (u v : UnitSection I M U) (x : U) :
    unitSectionEval (u + v) x = unitSectionEval u x * unitSectionEval v x := rfl

@[simp]
theorem unitSectionVal_neg (u : UnitSection I M U) :
    unitSectionVal (-u) = (u.toMul⁻¹).val := rfl

@[simp]
theorem unitSectionEval_neg (u : UnitSection I M U) (x : U) :
    unitSectionEval (-u) x = (unitSectionEval u x)⁻¹ := by
  exact map_units_inv
    (ContMDiffMap.evalRingHom (I := I) (I' := modelWithCornersSelf ℂ ℂ) (n := ω) x)
    u.toMul

variable (I M)

/-- Restriction is the actual morphism of the composed sheaf, bundled as an
additive homomorphism between its definitionally equal section groups. -/
def unitRestriction {U V : Opens M} (h : U ≤ V) :
    UnitSection I M V →+ UnitSection I M U :=
  ((unitsSheaf I M).presheaf.map (homOfLE h).op).hom

theorem unitRestriction_eq_map {U V : Opens M} (h : U ≤ V) :
    AddCommGrpCat.ofHom (unitRestriction I M h) =
      (unitsSheaf I M).presheaf.map (homOfLE h).op := rfl

@[simp]
theorem unitSectionVal_restrict {U V : Opens M} (h : U ≤ V)
    (u : UnitSection I M V) :
    unitSectionVal ((unitsSheaf I M).presheaf.map (homOfLE h).op u) =
      (HolomorphicFunctionSheaf.sheaf I M).presheaf.map (homOfLE h).op
        (unitSectionVal u) := rfl

/-- The actual sheaf restriction evaluates by literal function restriction. -/
@[simp]
theorem unitSectionEval_restrict {U V : Opens M} (h : U ≤ V)
    (u : UnitSection I M V) (x : U) :
    unitSectionEval ((unitsSheaf I M).presheaf.map (homOfLE h).op u) x =
      unitSectionEval u ⟨x, h x.property⟩ := rfl

@[simp]
theorem unitRestriction_val {U V : Opens M} (h : U ≤ V)
    (u : UnitSection I M V) :
    unitSectionVal (unitRestriction I M h u) =
      HolomorphicFunctionSheaf.restrictionAlgHom I M h (unitSectionVal u) := rfl

@[simp]
theorem unitRestriction_eval {U V : Opens M} (h : U ≤ V)
    (u : UnitSection I M V) (x : U) :
    unitSectionEval (unitRestriction I M h u) x =
      unitSectionEval u ⟨x, h x.property⟩ := rfl

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
