import StackExchange.Puzzling139335.HalfTurnRemainder.Holes
import StackExchange.Puzzling139335.HalfTurnRemainder.ConnectedInterior

/-!
# The hole dichotomy for an actual square dissection

If two pieces are exchanged by the central half-turn and the square center is
strictly inside a remaining piece, the remaining union has either no holes or
exactly the interiors of the two removed pieces as its holes.
-/

open Set

namespace Puzzling139335.SquareDissection

open HalfTurnRemainder

/-- The actual remainder of a central half-turn pair has zero or two holes. -/
theorem pair_remainder_hole_dichotomy (d : SquareDissection)
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 2 = d.piece 3)
    (hc : squareCenter ∈ interior (d.piece 0)) :
    boundedComplementComponents (d.piece 0 ∪ d.piece 1) = ∅ ∨
      boundedComplementComponents (d.piece 0 ∪ d.piece 1) =
        {interior (d.piece 2), interior (d.piece 3)} := by
  exact boundedComplementComponents_empty_or_eq_interiors_of_pointReflection
    ((d.jordan 0).isClosed.union (d.jordan 1).isClosed)
    (union_subset (d.piece_subset 0) (d.piece_subset 1))
    d.four_piece_pair_union.ge (d.jordan 2) (d.jordan 3)
    (disjoint_union_right.mpr ⟨d.disjoint_interior_piece (by decide),
      d.disjoint_interior_piece (by decide)⟩)
    (disjoint_union_right.mpr ⟨d.disjoint_interior_piece (by decide),
      d.disjoint_interior_piece (by decide)⟩)
    (d.pair_remainder_isConnected hpair hc) (Or.inl (interior_subset hc))
    (d.pair_remainder_pointReflection hpair)

end Puzzling139335.SquareDissection
