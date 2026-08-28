import Wikipedia.HopfProblem.PeriodDomain
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRepresentation

/-!
# Triangle-group invariance of the period discriminant

Invariance under the two actual Möbius generators extends to every element
of the constructed triangle group.  Applied to the period discriminant, this
uses the proved generator transformation formulas and requires no additional
global invariance assumption.
-/

noncomputable section

open UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.Construction

/-- Invariance under the two distinguished Möbius generators implies
invariance under the actual representation of every triangle-group element.
The codomain carries no algebraic or topological assumptions. -/
theorem triangle_invariant_of_generators {A : Type*} (f : ℍ → A)
    (h₁ : ∀ z, f (Triangle.generatorOneSL • z) = f z)
    (h₂ : ∀ z, f (Triangle.generatorTwoSL • z) = f z)
    (g : TriangleGroup) :
    ∀ z, f (triangleGeometricRepresentation g z) = f z := by
  let := triangleGeometricAction
  have hg : g ∈ Subgroup.closure
      ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) := by
    rw [triangle_generators_generate]
    trivial
  change ∀ z, f (g • z) = f z
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with rfl | rfl
    · intro z
      change f (triangleGeometricRepresentation triangleGenerator₁ z) = f z
      simpa only [triangleGeometricRepresentation_generator₁_apply] using h₁ z
    · intro z
      change f (triangleGeometricRepresentation triangleGenerator₂ z) = f z
      simpa only [triangleGeometricRepresentation_generator₂_apply] using h₂ z
  | one => intro z; rw [one_smul]
  | mul g h _ _ ihg ihh => intro z; rw [mul_smul, ihg, ihh]
  | inv g _ ih =>
    intro z
    simpa only [smul_inv_smul] using (ih (g⁻¹ • z)).symm

/-- The discriminant of a period map satisfying the two generator laws is
invariant under the whole actual triangle-group representation. -/
theorem discriminant_invariant_of_generator_laws (P : ℍ → PeriodPoint)
    (hτ : ∀ z, 0 < (P z).τ.im)
    (h₁ : ∀ z, P (Triangle.generatorOneSL • z) = (P z).step₁)
    (h₂ : ∀ z, P (Triangle.generatorTwoSL • z) = (P z).step₂) :
    ∀ (g : TriangleGroup) (z : ℍ),
      (P (triangleGeometricRepresentation g z)).discriminant = (P z).discriminant := by
  apply triangle_invariant_of_generators (fun z => (P z).discriminant)
  · intro z
    rw [h₁ z, PeriodPoint.step₁_discriminant (P z) (ne_of_gt (hτ z))]
  · intro z
    rw [h₂ z, PeriodPoint.step₂_discriminant (P z) (ne_of_gt (hτ z))]

end Wikipedia.HopfProblem.SpecialPeriods.Construction
