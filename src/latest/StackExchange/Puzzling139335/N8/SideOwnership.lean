import StackExchange.Puzzling139335.N8.SideOwnership.BoundaryArc
import StackExchange.Puzzling139335.N8.SideOwnership.Geometry
import StackExchange.Puzzling139335.CornerIncidence

/-!
# Full-side ownership from adjacent-corner contacts

A piece containing two adjacent square corners owns the full intervening
side if every other piece contains some corner outside that pair.  This uses
the actual boundary segment and access arcs in the Jordan pieces; no segment
in a convex hull is substituted for a segment in a piece.
-/

open Set

namespace Puzzling139335

namespace SquareDissection

/-- A competing piece that contains a corner outside the chosen side cannot
meet the side away from its endpoints. -/
theorem side_sdiff_disjoint_of_external_corner
    (d : SquareDissection) {i j a c : Fin 4} (hji : j ≠ i)
    (hleft : corner a ∈ d.piece i) (hright : corner (a + 1) ∈ d.piece i)
    (hc : corner c ∈ d.piece j) (hca : c ≠ a) (hca1 : c ≠ a + 1) :
    Disjoint (segment ℝ (corner a) (corner (a + 1)) \ {corner a, corner (a + 1)})
      (d.piece j) := by
  apply N8.boundary_arc_sdiff_disjoint_of_external_contact
    (d.jordan i) (d.jordan j) isJordanRegion_unitSquare
    (d.piece_subset i) (d.piece_subset j)
    (d.disjoint_interiors (fun hij => hji hij.symm))
    (N8.side_segment_isArcBetween a) (N8.side_segment_subset_frontier_unitSquare a)
    hleft hright hc
  · exact corner_mem_frontier_of_subset (Subset.refl unitSquare) (corner_mem_unitSquare c)
  · exact fun hseg => ((N8.corner_mem_side_segment_iff a c).mp hseg).elim hca hca1

/-- If every other piece contains a corner outside an adjacent pair owned by
one piece, that piece contains the entire actual side between the pair. -/
theorem side_subset_of_other_pieces_have_external_corner
    (d : SquareDissection) (i a : Fin 4)
    (hleft : corner a ∈ d.piece i) (hright : corner (a + 1) ∈ d.piece i)
    (hothers : ∀ j, j ≠ i → ∃ c, c ≠ a ∧ c ≠ a + 1 ∧ corner c ∈ d.piece j) :
    segment ℝ (corner a) (corner (a + 1)) ⊆ d.piece i := by
  apply d.boundary_arc_subset_of_other_pieces_have_external_contact
    (N8.side_segment_isArcBetween a) (N8.side_segment_subset_frontier_unitSquare a)
    hleft hright
  intro j hji
  obtain ⟨c, hca, hca1, hc⟩ := hothers j hji
  refine ⟨corner c, hc, ?_, ?_⟩
  · exact corner_mem_frontier_of_subset (Subset.refl unitSquare) (corner_mem_unitSquare c)
  · exact fun hseg => ((N8.corner_mem_side_segment_iff a c).mp hseg).elim hca hca1

/-- The forced side is on the actual frontier of the owning piece. -/
theorem side_subset_frontier_of_other_pieces_have_external_corner
    (d : SquareDissection) (i a : Fin 4)
    (hleft : corner a ∈ d.piece i) (hright : corner (a + 1) ∈ d.piece i)
    (hothers : ∀ j, j ≠ i → ∃ c, c ≠ a ∧ c ≠ a + 1 ∧ corner c ∈ d.piece j) :
    segment ℝ (corner a) (corner (a + 1)) ⊆ frontier (d.piece i) := by
  intro z hz
  exact RectangularHull.mem_frontier_of_subset (d.piece_subset i)
    (d.side_subset_of_other_pieces_have_external_corner i a hleft hright hothers hz)
    (N8.side_segment_subset_frontier_unitSquare a hz)

end SquareDissection

end Puzzling139335
