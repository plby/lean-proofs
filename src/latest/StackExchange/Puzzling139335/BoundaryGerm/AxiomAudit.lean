import StackExchange.Puzzling139335.SharedCornerStraightCount.Double
import StackExchange.Puzzling139335.BoundaryGerm.Segments

open Set

/-!
# Kernel dependency audit for the actual boundary-germ parity bridge

These declarations instantiate the complete interface construction and the
straight-branch conclusions.  The printed dependency lists make explicit
that no polygonality, tangent, local-sector, or additional topology axiom
has been introduced.
-/

#print axioms Puzzling139335.SquareDissection.exists_exact_boundary_arc_family
#print axioms Puzzling139335.ExactBoundaryArcFamily.mate_involutive
#print axioms Puzzling139335.HasStraightBranchCount.unique
#print axioms Puzzling139335.HasStraightBranchCount.exists_two_segments
#print axioms Puzzling139335.HasStraightBranchCount.one_image_straight_arc_sameBoundaryGerm
#print axioms Puzzling139335.SameBoundaryGerm.segments_sameRay
#print axioms Puzzling139335.ExactBoundaryArcFamily.hasStraightBranchCount_straightBoundaryOccurrences
#print axioms Puzzling139335.ExactBoundaryArcFamily.card_exterior_straightOccurrences_corner
#print axioms Puzzling139335.SquareDissection.hasStraightBranchCount_two_of_three_equal_intrinsic
#print axioms Puzzling139335.SquareDissection.hasStraightBranchCount_one_or_two_of_two_equal_intrinsic

namespace Puzzling139335

example (d : SquareDissection) (j : Fin 4) (a : Plane)
    (hthree : d.cornerTileCount j = 3)
    (htype : ∀ i : Fin 4, corner j ∈ d.piece i → d.intrinsicCorner i j = a) :
    HasStraightBranchCount (frontier (d.piece 0)) a 2 :=
  d.hasStraightBranchCount_two_of_three_equal_intrinsic j a hthree htype

example (d : SquareDissection) (j : Fin 4) (a : Plane)
    (htwo : d.cornerTileCount j = 2)
    (htype : ∀ i : Fin 4, corner j ∈ d.piece i → d.intrinsicCorner i j = a) :
    HasStraightBranchCount (frontier (d.piece 0)) a 1 ∨
      HasStraightBranchCount (frontier (d.piece 0)) a 2 :=
  d.hasStraightBranchCount_one_or_two_of_two_equal_intrinsic j a htwo htype

end Puzzling139335
