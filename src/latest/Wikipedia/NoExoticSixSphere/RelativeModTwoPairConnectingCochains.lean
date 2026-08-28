import Wikipedia.NoExoticSixSphere.CochainConnectingRepresentatives
import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainSequence

/-!
# Genuine cochain lifts for the connecting map of a pair

The original short exact cochain row supplies an ambient extension and
a relative cocycle whose absolute cochain is its coboundary. The class
of this cocycle is the actual pair connecting homomorphism.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris SingularCohomologyFree

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem exists_pair_connecting_cochains (p : ℕ) (α : ModTwoCapProduct.Cocycle U p) :
    ∃ (β : ModTwoCapProduct.Cochain X p) (γ : Cocycle U (p + 1)),
      ModTwoCapProduct.pullback (subtypeInclusion U) p β = α.val ∧
      toAbsolute U (p + 1) γ.val = ModTwoCapProduct.coboundary β ∧
      connecting U p (cocycleClass (ModTwoCapProduct.cochainComplex U) p α) =
        cocycleClass (complex U) (p + 1) γ := by
  obtain ⟨β, hβ, γ, hγ, he⟩ :=
    CochainConnecting.exists_connecting_lift (sequence_shortExact U) p α
  exact ⟨β, γ, hβ, hγ, he⟩

end NoExoticSixSphere.RelativeModTwoCochains
