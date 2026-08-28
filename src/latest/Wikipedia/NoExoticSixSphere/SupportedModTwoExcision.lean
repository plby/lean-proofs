import Wikipedia.NoExoticSixSphere.RelativeModTwoExcision
import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology

/-!
# Excision of a closed support into an actual open neighborhood

An open neighborhood of the closed support and its open complement
cover the ambient space. The original relative cohomology excision
equivalence is therefore the actual restriction to that neighborhood.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X] (U K : Set X)

omit [TopologicalSpace X] in
theorem neighborhood_complement_cover (hKU : K ⊆ U) : U ∪ Kᶜ = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ K
  · exact Or.inl (hKU hx)
  · exact Or.inr hx

/-- Actual supported cohomology is unchanged by restricting to an open neighborhood. -/
def neighborhoodEquiv (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (p : ℕ) :
    Cohomology K p ≃ₗ[ℤ] Cohomology (Subtype.val ⁻¹' K : Set U) p :=
  RelativeModTwoCochains.excisionEquiv U Kᶜ hU hK.isOpen_compl
    (neighborhood_complement_cover U K hKU) p

/-- The forward map is the original pair pullback, not a chosen abstract isomorphism. -/
theorem neighborhoodEquiv_toLinearMap (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) (p : ℕ) :
    (neighborhoodEquiv U K hU hK hKU p).toLinearMap =
      RelativeModTwoCochains.cohomologyPullback (subtypeInclusion U)
        (show Set.MapsTo (subtypeInclusion U) (Subtype.val ⁻¹' K : Set U)ᶜ Kᶜ
          from fun _ hx => hx) p := rfl

end NoExoticSixSphere.SupportedModTwoCohomology
