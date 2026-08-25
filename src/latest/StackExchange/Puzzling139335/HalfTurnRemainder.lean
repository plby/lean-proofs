import StackExchange.Puzzling139335.HalfTurnRemainder.NoHoles
import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion

/-!
# The genuine Jordan remainder of an actual half-turn pair

Suppose pieces 2 and 3 of an actual square dissection are exchanged by the
half-turn about the square center and piece 0 contains the center in its
interior. The union of pieces 0 and 1 is centrally symmetric, has connected
interior and connected complement, and is a Jordan region. Their entire
intersection is one nondegenerate proper Jordan crosscut; the original pieces
are exactly the two closed sides of that cut.

The imported proofs derive symmetry from regular closedness and coverage,
connectedness from the center component and Brouwer, and absence of holes
from actual finite paired interfaces and truncated variation. The final
two-region topology uses inversion and Jordan crosscut separation. No Jordan
remainder, hole exclusion, connected intersection or proper-cut hypothesis is
added to the original dissection assumptions.

The separate central two-piece theorem is not asserted in this module. The
results here supply its actual geometric input.
-/

open Set Schoenflies

namespace Puzzling139335.SquareDissection

/-- Full Jordan-remainder conclusion from an actual half-turn pair and the
protected center, with both connectivity inputs discharged. -/
theorem pair_remainder_jordan (d : SquareDissection)
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 2 = d.piece 3)
    (hc : squareCenter ∈ interior (d.piece 0)) :
    IsJordanRegion (d.piece 0 ∪ d.piece 1) ∧ ∃ p q M N,
      JordanCrosscut (frontier (d.piece 0 ∪ d.piece 1))
        (d.piece 0 ∩ d.piece 1) p q ∧
      IsCutPair (frontier (d.piece 0 ∪ d.piece 1)) p q M N ∧
      d.piece 0 = closure (inside (M ∪ (d.piece 0 ∩ d.piece 1))) ∧
      d.piece 1 = closure (inside (N ∪ (d.piece 0 ∩ d.piece 1))) :=
  d.pair_remainder_jordan_of_connected
    (d.pair_remainder_isConnected_interior hpair hc)
    (d.pair_remainder_isConnected_compl hpair hc)

/-- The actual outer Jordan boundary of the remainder is centrally symmetric. -/
theorem pair_remainder_frontier_pointReflection (d : SquareDissection)
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 2 = d.piece 3) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter ''
      frontier (d.piece 0 ∪ d.piece 1) = frontier (d.piece 0 ∪ d.piece 1) :=
  ((AffineIsometryEquiv.pointReflection ℝ squareCenter).toHomeomorph.image_frontier _).trans
    (congrArg frontier (d.pair_remainder_pointReflection hpair))

/-- The protected center is absent from the actual common cut. -/
theorem pair_remainder_center_not_mem_inter (d : SquareDissection)
    (hc : squareCenter ∈ interior (d.piece 0)) :
    squareCenter ∉ d.piece 0 ∩ d.piece 1 :=
  fun hx => d.not_mem_other_piece (by decide : (0 : Fin 4) ≠ 1) hc hx.2

/-- The same geometric reduction after any actual relabeling of the four
pieces; labels 0,1 are retained and labels 2,3 are the half-turn pair. -/
theorem reindexed_pair_remainder_jordan (d : SquareDissection) (σ : Equiv.Perm (Fin 4))
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece (σ 2) = d.piece (σ 3))
    (hc : squareCenter ∈ interior (d.piece (σ 0))) :
    IsJordanRegion (d.piece (σ 0) ∪ d.piece (σ 1)) ∧ ∃ p q M N,
      JordanCrosscut (frontier (d.piece (σ 0) ∪ d.piece (σ 1)))
        (d.piece (σ 0) ∩ d.piece (σ 1)) p q ∧
      IsCutPair (frontier (d.piece (σ 0) ∪ d.piece (σ 1))) p q M N ∧
      d.piece (σ 0) = closure (inside (M ∪ (d.piece (σ 0) ∩ d.piece (σ 1)))) ∧
      d.piece (σ 1) = closure (inside (N ∪ (d.piece (σ 0) ∩ d.piece (σ 1)))) := by
  exact (d.reindex σ).pair_remainder_jordan hpair hc

end Puzzling139335.SquareDissection
