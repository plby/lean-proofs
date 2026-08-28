import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorDivisionInvariance
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorDivisionLocal

/-!
# Global holomorphic division of homogeneous μ sections

Two actual homogeneous generator laws and exact central zero orders
produce a global holomorphic invariant quotient.  At the two elliptic
orbits the values come from constructed analytic division germs; at every
other point the function is the ordinary quotient.  Holomorphicity at
all translated elliptic points follows from the actual biholomorphic
triangle action.  No global factor or holomorphic quotient is assumed.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Division

/-- Orbitwise completion preserves the proved all-word invariance of
the ordinary pointwise quotient, even at its zero denominators. -/
theorem completedQuotient_invariant {ν F : ℍ → ℂ} (v : Elliptic.Kind → ℂ)
    (hinv : ∀ g : TriangleGroup, ∀ z : ℍ,
      ν (triangleGeometricRepresentation g z) / F (triangleGeometricRepresentation g z) =
        ν z / F z)
    (g : TriangleGroup) (z : ℍ) :
    completedQuotient ν F v (triangleGeometricRepresentation g z) =
      completedQuotient ν F v z := by
  unfold completedQuotient
  rw [triangleOrbitProjection_smul g z, hinv g z]

/-- The completed quotient really factors the numerator everywhere,
including the actual elliptic zero set. -/
theorem completedQuotient_factorization {ν F : ℍ → ℂ}
    (hFzero : ∀ z : ℍ, F z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo)
    (hνzero : ∀ z : ℍ, F z = 0 → ν z = 0)
    (v : Elliptic.Kind → ℂ) (z : ℍ) :
    ν z = F z * completedQuotient ν F v z := by
  by_cases hz : F z = 0
  · rw [hz, hνzero z hz, zero_mul]
  · have hn : ¬(triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo) :=
      fun he => hz ((hFzero z).mpr he)
    rw [completedQuotient_eq_div ν F v z (fun h => hn (.inl h)) (fun h => hn (.inr h))]
    exact (mul_div_cancel₀ (ν z) hz).symm.trans (by ring)

/-- Holomorphicity at the two actual elliptic centres suffices for the
completed invariant quotient, because every zero belongs to one of
their actual triangle orbits. -/
theorem completedQuotient_holomorphic {ν F : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hFzero : ∀ z : ℍ, F z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ)
    (hinv : ∀ g : TriangleGroup, ∀ z : ℍ,
      completedQuotient ν F v (triangleGeometricRepresentation g z) =
        completedQuotient ν F v z)
    (hcenter : ∀ j : Elliptic.Kind,
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v) (Triangle.ellipticCenter j)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v) := by
  intro z
  by_cases hz : F z = 0
  · rcases (hFzero z).mp hz with h₁ | h₂
    · obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff z Triangle.centerOne).mp h₁
      rw [← hg]
      exact contMDiffAt_orbit hinv (hcenter .three) g
    · obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff z Triangle.centerTwo).mp h₂
      rw [← hg]
      exact contMDiffAt_orbit hinv (hcenter .four) g
  · exact completedQuotient_contMDiffAt_of_ne_zero hν hF hFzero v z hz

/-- Every homogeneous section has a genuine global holomorphic
invariant factor after division by a denominator with the actual
elliptic zero set and exact orders two and one at its two centres.

The analytic removable values are constructed from the homogeneous
laws and the exact orders.  In particular, neither holomorphicity of
the quotient nor a global factorization is an input. -/
theorem exists_holomorphic_invariant_factor {τ : ℍ → ℍ} {ν F : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (hFzero : ∀ z : ℍ, F z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo)
    (hForder₁ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) = 2)
    (hForder₂ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1) :
    ∃ H : ℍ → ℂ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H ∧
      (∀ g : TriangleGroup, ∀ z : ℍ,
        H (triangleGeometricRepresentation g z) = H z) ∧
      ∀ z : ℍ, ν z = F z * H z := by
  obtain ⟨h₁, hh₁, he₁⟩ :=
    MuGenerator.exists_division_at_centerOne hτ hτc hν hν₁ hF hForder₁
  obtain ⟨h₂, hh₂, he₂⟩ :=
    MuGenerator.exists_division_at_centerTwo hν hν₂ hF hForder₂
  let v : Elliptic.Kind → ℂ
    | .three => h₁ (Triangle.centerOne : ℂ)
    | .four => h₂ (Triangle.centerTwo : ℂ)
  have hinv := completedQuotient_invariant v (quotient_invariant hν₁ hν₂ hF₁ hF₂)
  refine ⟨completedQuotient ν F v, ?_, hinv, ?_⟩
  · apply completedQuotient_holomorphic hν hF hFzero v hinv
    intro j
    cases j
    · exact completedQuotient_contMDiffAt_center hFzero v .three h₁ hh₁ rfl he₁
    · exact completedQuotient_contMDiffAt_center hFzero v .four h₂ hh₂ rfl he₂
  · apply completedQuotient_factorization hFzero
    intro z hz
    exact zero_of_ellipticOrbit hν₁ hν₂ ((hFzero z).mp hz)

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Division
