import Wikipedia.HopfProblem.HolomorphicExponentialSheafUnitsBasic
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Unit sections are exactly nowhere-zero holomorphic functions

The inverse of a nowhere-zero holomorphic section is its actual scalar
reciprocal, which is holomorphic in the original complex charts.  Thus no
local invertibility or gluing assumption is needed to identify the units
of the section ring with nowhere-zero sections.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {U : Opens M}

/-- The genuine pointwise inverse of a nowhere-zero holomorphic function. -/
def inverseSectionOfNonvanishing (f : HolomorphicFunctionSheaf.Section I M U)
    (hne : ∀ x, f x ≠ 0) : HolomorphicFunctionSheaf.Section I M U :=
  ⟨fun x => (f x)⁻¹, f.contMDiff.inv₀ hne⟩

@[simp]
theorem inverseSectionOfNonvanishing_apply
    (f : HolomorphicFunctionSheaf.Section I M U) (hne : ∀ x, f x ≠ 0) (x : U) :
    inverseSectionOfNonvanishing f hne x = (f x)⁻¹ := rfl

/-- A nowhere-zero holomorphic section defines an actual unit of its section
ring, written additively. -/
def unitSectionOfNonvanishing (f : HolomorphicFunctionSheaf.Section I M U)
    (hne : ∀ x, f x ≠ 0) : UnitSection I M U :=
  Additive.ofMul
    { val := f
      inv := inverseSectionOfNonvanishing f hne
      val_inv := by
        apply ContMDiffMap.ext
        intro x
        exact mul_inv_cancel₀ (hne x)
      inv_val := by
        apply ContMDiffMap.ext
        intro x
        exact inv_mul_cancel₀ (hne x) }

@[simp]
theorem unitSectionVal_unitSectionOfNonvanishing
    (f : HolomorphicFunctionSheaf.Section I M U) (hne : ∀ x, f x ≠ 0) :
    unitSectionVal (unitSectionOfNonvanishing f hne) = f := rfl

@[simp]
theorem unitSectionOfNonvanishing_eval
    (f : HolomorphicFunctionSheaf.Section I M U) (hne : ∀ x, f x ≠ 0) (x : U) :
    unitSectionEval (unitSectionOfNonvanishing f hne) x = f x := rfl

/-- Every actual unit section is nowhere zero. -/
theorem unitSectionEval_ne_zero (u : UnitSection I M U) (x : U) :
    unitSectionEval u x ≠ 0 := by
  have h : unitSectionEval u x * u.toMul.inv x = 1 :=
    congrArg (fun f : HolomorphicFunctionSheaf.Section I M U => f x) u.toMul.val_inv
  intro hx
  rw [hx, zero_mul] at h
  exact zero_ne_one h

@[simp]
theorem unitSectionOfNonvanishing_unitSectionVal (u : UnitSection I M U) :
    unitSectionOfNonvanishing (unitSectionVal u) (unitSectionEval_ne_zero u) = u := by
  apply unitSection_ext
  intro x
  rfl

/-- The algebraic and pointwise notions of invertibility agree for the actual
holomorphic section ring, including on the empty open set. -/
theorem isUnit_iff_nonvanishing (f : HolomorphicFunctionSheaf.Section I M U) :
    IsUnit f ↔ ∀ x, f x ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ x
    exact unitSectionEval_ne_zero (Additive.ofMul u) x
  · intro hne
    exact ⟨(unitSectionOfNonvanishing f hne).toMul, rfl⟩

/-- The unit built from a nonvanishing function restricts to the unit built
from the actual restricted function. -/
theorem unitSectionOfNonvanishing_restrict {V : Opens M} (h : U ≤ V)
    (f : HolomorphicFunctionSheaf.Section I M V) (hne : ∀ x, f x ≠ 0) :
    (unitsSheaf I M).presheaf.map (homOfLE h).op (unitSectionOfNonvanishing f hne) =
      unitSectionOfNonvanishing (HolomorphicFunctionSheaf.restrictionAlgHom I M h f)
        (fun x => hne ⟨x, h x.property⟩) := by
  apply unitSection_ext
  intro x
  rfl

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
