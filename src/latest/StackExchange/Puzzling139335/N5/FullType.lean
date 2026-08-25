import StackExchange.Puzzling139335.RepeatedCorners
import StackExchange.Puzzling139335.DissectionTopology
import StackExchange.Puzzling139335.ThreeCorners.FullCorners

/-!
# Unsplit intrinsic corner types remain unsplit

A tile containing a full relative square neighborhood at a point excludes
every other tile there: any other Jordan tile is the closure of its
interior.  Equal intrinsic corner types transport the full neighborhood by
an actual square symmetry.  These statements do not assume a particular
corner-incidence count or any boundary-angle regularity.
-/

open Set Metric

namespace Puzzling139335.N5

/-- A full relative neighborhood in one tile excludes all the other tiles,
including at boundary points of the square. -/
theorem unique_piece_of_relative_neighborhood (d : SquareDissection)
    (i : Fin 4) {p : Plane} {ε : ℝ} (hε : 0 < ε)
    (hnear : ball p ε ∩ unitSquare ⊆ d.piece i) :
    ∀ m, m ≠ i → p ∉ d.piece m := by
  intro m hmi hpm
  have hpcl : p ∈ closure (interior (d.piece m)) := by
    rwa [(d.jordan m).closure_interior]
  obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.mp hpcl ε hε
  have hqi : q ∈ d.piece i := hnear
    ⟨mem_ball.mpr (by simpa only [dist_comm] using hdist),
      d.piece_subset m (interior_subset hq)⟩
  exact d.not_mem_other_piece hmi hq hqi

/-- An actual square symmetry transports relative neighborhoods along
with the tile. -/
theorem relative_neighborhood_map (e : Plane ≃ᵃⁱ[ℝ] Plane)
    {P Q : Set Plane} {p q : Plane} {ε : ℝ}
    (hP : e '' P = Q) (hS : e '' unitSquare = unitSquare) (hp : e p = q)
    (hnear : ball p ε ∩ unitSquare ⊆ P) :
    ball q ε ∩ unitSquare ⊆ Q := by
  have hball : e '' ball p ε = ball (e p) ε := e.toIsometryEquiv.image_ball p ε
  have himage : e '' (ball p ε ∩ unitSquare) = ball q ε ∩ unitSquare := by
    rw [Set.image_inter e.injective, hball, hp, hS]
  rw [← himage, ← hP]
  exact image_mono hnear

/-- An intrinsic point used at an unsplit corner cannot occur at a split
corner in another chosen placement. -/
theorem unique_corner_of_equal_intrinsicCorner (d : SquareDissection)
    {i j k l : Fin 4}
    (hunique : ∀ m, m ≠ i → corner j ∉ d.piece m)
    (htype : d.intrinsicCorner i j = d.intrinsicCorner k l) :
    ∀ m, m ≠ k → corner l ∉ d.piece m := by
  obtain ⟨ε, hε, hnear⟩ := d.unique_piece_relative_neighborhood i hunique
  apply unique_piece_of_relative_neighborhood d k hε
  exact relative_neighborhood_map (d.relativePlacement i k)
    (d.relativePlacement_image i k)
    (d.relativePlacement_preserves_square_of_unique_corner hunique htype)
    (d.relativePlacement_corner htype) hnear

/-- The prototype point of a uniquely owned physical corner is an actual
full square corner in the sense of the placement-based definition. -/
theorem isFullSquareCorner_of_unique_corner (d : SquareDissection)
    (i j : Fin 4) (hunique : ∀ m, m ≠ i → corner j ∉ d.piece m) :
    UnitPairs.IsFullSquareCorner (d.piece 0) (d.intrinsicCorner i j) := by
  obtain ⟨ε, hε, hnear⟩ := d.unique_piece_relative_neighborhood i hunique
  refine ⟨d.placement i, j, ε, hε, ?_, d.placement_intrinsicCorner i j, ?_⟩
  · rw [d.placement_image]
    exact d.piece_subset i
  · simpa only [d.placement_image] using hnear

end Puzzling139335.N5
