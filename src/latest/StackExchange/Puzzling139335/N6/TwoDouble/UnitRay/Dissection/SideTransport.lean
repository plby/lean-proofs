import StackExchange.Puzzling139335.N8.SideOwnership.Geometry
import StackExchange.Puzzling139335.N8.Pairs
import StackExchange.Puzzling139335.RectangularHull.Interlacing.Regions
import StackExchange.Puzzling139335.Transform

/-!
# Transporting an actual square side

A square-side segment contained in a piece lies on that piece's frontier.
An actual congruence and a corner normalization transport the whole
segment to a frontier segment of length one based at the origin.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.UnitRay

open SquareSymmetry

/-- A whole square side contained in a piece is an actual frontier segment
of that piece, in either orientation of the two adjacent endpoints. -/
theorem actual_side_segment_frontier (d : SquareDissection) (i j m : Fin 4)
    (hseg : segment ℝ (corner j) (corner m) ⊆ d.piece i)
    (hadj : m = j + 1 ∨ j = m + 1) :
    segment ℝ (corner j) (corner m) ⊆ frontier (d.piece i) := by
  have hs : segment ℝ (corner j) (corner m) ⊆ frontier unitSquare := by
    rcases hadj with rfl | rfl
    · exact N8.side_segment_subset_frontier_unitSquare j
    · rw [segment_symm]
      exact N8.side_segment_subset_frontier_unitSquare m
  intro p hp
  exact RectangularHull.mem_frontier_of_subset (d.piece_subset i) (hseg hp) (hs hp)

/-- Transporting an actual side to a square corner gives a unit frontier
segment after normalizing that corner to the origin. -/
theorem transported_unit_side_segment (d : SquareDissection) {i k j m l : Fin 4}
    (hseg : segment ℝ (corner j) (corner m) ⊆ d.piece i)
    (hadj : m = j + 1 ∨ j = m + 1)
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hf : f '' d.piece i = d.piece k)
    (hcorner : f (corner j) = corner l) :
    ‖cornerFlip l (f (corner m))‖ = 1 ∧
      segment ℝ 0 (cornerFlip l (f (corner m))) ⊆
        frontier (cornerFlip l '' d.piece k) := by
  have hunit : dist (corner j) (corner m) = 1 := by
    rcases hadj with rfl | rfl
    · exact N8.dist_adjacent_corners j
    · rw [dist_comm]
      exact N8.dist_adjacent_corners m
  have hzero : cornerFlip l (f (corner j)) = 0 := by
    rw [hcorner, cornerFlip_corner]
  have hfront : segment ℝ (corner j) (corner m) ⊆ frontier (d.piece i) :=
    actual_side_segment_frontier d i j m hseg hadj
  have himage : f '' segment ℝ (corner j) (corner m) =
      segment ℝ (f (corner j)) (f (corner m)) :=
    image_segment ℝ f.toAffineMap _ _
  have hflip : cornerFlip l '' segment ℝ (f (corner j)) (f (corner m)) =
      segment ℝ 0 (cornerFlip l (f (corner m))) := by
    calc
      cornerFlip l '' segment ℝ (f (corner j)) (f (corner m)) =
          segment ℝ (cornerFlip l (f (corner j))) (cornerFlip l (f (corner m))) :=
        image_segment ℝ (cornerFlip l).toAffineMap _ _
      _ = segment ℝ 0 (cornerFlip l (f (corner m))) := by rw [hzero]
  constructor
  · calc
      ‖cornerFlip l (f (corner m))‖ =
          dist (cornerFlip l (f (corner j))) (cornerFlip l (f (corner m))) := by
        rw [hzero, dist_zero_left]
      _ = dist (f (corner j)) (f (corner m)) := (cornerFlip l).isometry.dist_eq _ _
      _ = dist (corner j) (corner m) := f.isometry.dist_eq _ _
      _ = 1 := hunit
  · have hfrontImage : f '' frontier (d.piece i) = frontier (d.piece k) := by
      calc
        f '' frontier (d.piece i) = frontier (f '' d.piece i) :=
          f.toHomeomorph.image_frontier _
        _ = frontier (d.piece k) := congrArg frontier hf
    have hfrontFlip : cornerFlip l '' frontier (d.piece k) =
        frontier (cornerFlip l '' d.piece k) :=
      (cornerFlip l).toHomeomorph.image_frontier _
    rw [← hflip, ← himage, ← hfrontFlip, ← hfrontImage]
    exact image_mono (image_mono hfront)

end Puzzling139335.N6.TwoDouble.UnitRay
