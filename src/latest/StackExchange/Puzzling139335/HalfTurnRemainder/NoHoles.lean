import StackExchange.Puzzling139335.HalfTurnRemainder.Holes.Actual
import StackExchange.Puzzling139335.HalfTurnRemainder.Holes.ConnectedComplement
import StackExchange.Puzzling139335.HalfTurnRemainder.Variation.NoTwoHoles

/-!
# The actual half-turn remainder has no holes

The topological dichotomy leaves zero holes or exactly the two omitted tile
interiors. The latter is excluded by the concrete finite-interface variation
argument. The remainder's whole complement is therefore connected.
-/

open Set

namespace Puzzling139335.SquareDissection

open HalfTurnRemainder

/-- No bounded complementary component exists for the actual remainder of a
half-turn pair when another piece contains a neighborhood of the center. -/
theorem pair_remainder_no_holes (d : SquareDissection)
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 2 = d.piece 3)
    (hc : squareCenter ∈ interior (d.piece 0)) :
    boundedComplementComponents (d.piece 0 ∪ d.piece 1) = ∅ := by
  rcases d.pair_remainder_hole_dichotomy hpair hc with hnone | htwo
  · exact hnone
  · have h₂ : interior (d.piece 2) ∈ boundedComplementComponents (d.piece 0 ∪ d.piece 1) := by
      rw [htwo]
      exact Or.inl rfl
    have h₃ : interior (d.piece 3) ∈ boundedComplementComponents (d.piece 0 ∪ d.piece 1) := by
      rw [htwo]
      exact Or.inr rfl
    obtain ⟨x₂, _, hcomp₂, _⟩ := h₂
    obtain ⟨x₃, _, hcomp₃, _⟩ := h₃
    exact False.elim (two_hole_components_impossible d hcomp₂.symm hcomp₃.symm)

/-- The complete complement of the actual half-turn remainder is connected. -/
theorem pair_remainder_isConnected_compl (d : SquareDissection)
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 2 = d.piece 3)
    (hc : squareCenter ∈ interior (d.piece 0)) :
    IsConnected (d.piece 0 ∪ d.piece 1)ᶜ :=
  isConnected_compl_of_no_bounded_square_components
    (union_subset (d.piece_subset 0) (d.piece_subset 1)) (d.pair_remainder_no_holes hpair hc)

end Puzzling139335.SquareDissection
