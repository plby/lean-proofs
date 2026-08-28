import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorTransform
import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorLocalDivision
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientBasic

/-!
# Algebraic invariance for homogeneous mu division

Two functions obeying the same homogeneous laws have an invariant
pointwise quotient under the entire actual triangle action.  This identity
uses the field's total division, including at denominator zeros; it does
not assert holomorphy of that pointwise quotient.

The zero set of any homogeneous section is likewise invariant.  Its
forced zeros at the two elliptic centres therefore propagate to their
entire actual triangle orbits.  None of these statements requires
holomorphic hypotheses.
-/

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Division

/-- The pointwise ratio of two functions with the same homogeneous laws
is invariant under every element of the actual triangle group. -/
theorem quotient_invariant {τ : ℍ → ℍ} {ν F : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (g : TriangleGroup) (z : ℍ) :
    ν (triangleGeometricRepresentation g z) /
        F (triangleGeometricRepresentation g z) = ν z / F z := by
  apply MuGenerator.triangle_invariant_of_generators (fun w => ν w / F w) _ _ g z
  · intro w
    rw [hν₁, hF₁, div_div_div_cancel_right₀ (τ w).ne_zero, neg_div_neg_eq]
  · intro w
    rw [hν₂, hF₂, div_div_div_cancel_right₀ (τ w).ne_zero]

/-- The actual triangle action preserves the zero set of a homogeneous
section, without any regularity assumptions on that section. -/
theorem zero_invariant {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (g : TriangleGroup) (z : ℍ) :
    ν (triangleGeometricRepresentation g z) = 0 ↔ ν z = 0 := by
  have h := quotient_invariant hν₁ hν₂ hν₁ hν₂ g z
  have hz : ν (triangleGeometricRepresentation g z) /
        ν (triangleGeometricRepresentation g z) = 0 ↔ ν z / ν z = 0 := by
    rw [h]
  simpa only [div_eq_zero_iff, or_self] using hz

/-- Every point in the first elliptic orbit is a zero of a homogeneous
section, as follows from its generator laws alone. -/
theorem zero_of_centerOneOrbit {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    {z : ℍ} (hz : triangleOrbitProjection z = triangleOrbitCenterOne) :
    ν z = 0 := by
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff z Triangle.centerOne).mp hz
  rw [← hg]
  exact (zero_invariant hν₁ hν₂ g Triangle.centerOne).mpr
    (MuGenerator.homogeneous_centerOne_eq_zero hν₁)

/-- Every point in the second elliptic orbit is likewise a forced zero. -/
theorem zero_of_centerTwoOrbit {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    {z : ℍ} (hz : triangleOrbitProjection z = triangleOrbitCenterTwo) :
    ν z = 0 := by
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff z Triangle.centerTwo).mp hz
  rw [← hg]
  exact (zero_invariant hν₁ hν₂ g Triangle.centerTwo).mpr
    (MuGenerator.homogeneous_centerTwo_eq_zero hν₂)

/-- Both actual elliptic orbits lie in the zero set of every homogeneous
section. -/
theorem zero_of_ellipticOrbit {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    {z : ℍ} (hz : triangleOrbitProjection z = triangleOrbitCenterOne ∨
      triangleOrbitProjection z = triangleOrbitCenterTwo) : ν z = 0 :=
  hz.elim (zero_of_centerOneOrbit hν₁ hν₂) (zero_of_centerTwoOrbit hν₁ hν₂)

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Division
