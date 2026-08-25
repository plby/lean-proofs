import StackExchange.Puzzling139335.RectangularHull.HeightBarrier
import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.BandMass.Geometry

/-!
# The lower cap contains the actual bottom side

The reflected upper piece contains a top corner, as does the other cornered
piece.  Regular closedness gives interior points above the midline in both.
Openness gives such a point in the center-containing piece.  The existing
Jordan crosscut height barrier then forces the entire bottom side into the
lower piece.  No straight-boundary or convexity assumption is used.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.HorizontalAcute

/-- A height attained strictly above a threshold by a Jordan region is
also exceeded by an interior point of that region. -/
theorem exists_interior_above_of_mem_height {P : Set Plane} {p : Plane} {h : ℝ}
    (hP : IsJordanRegion P) (hp : p ∈ P) (hh : h < p 1) :
    ∃ q ∈ interior P, h < q 1 := by
  by_contra hnone
  have hint : interior P ⊆ {q : Plane | q 1 ≤ h} := by
    intro q hq
    exact le_of_not_gt (fun hgt => hnone ⟨q, hq, hgt⟩)
  have hclosed : IsClosed {q : Plane | q 1 ≤ h} :=
    isClosed_le (Schoenflies.Plane.continuous_coord 1) continuous_const
  have hbound : P ⊆ {q : Plane | q 1 ≤ h} := by
    rw [← hP.closure_interior]
    exact closure_minimal hint hclosed
  exact (not_le_of_gt hh) (hbound hp)

/-- An open neighborhood of the square center contains a point strictly
above the midline.  The assertion does not require that `P` be Jordan. -/
theorem exists_interior_above_of_center {P : Set Plane}
    (hPS : P ⊆ unitSquare) (hc : squareCenter ∈ interior P) :
    ∃ q ∈ interior P, (1 / 2 : ℝ) < q 1 := by
  by_contra hnone
  have hint : interior P ⊆ horizontalBand 0 (1 / 2) := by
    intro q hq
    have hqS := hPS (interior_subset hq)
    exact ⟨hqS.1, hqS.2.1, le_of_not_gt (fun hgt => hnone ⟨q, hq, hgt⟩)⟩
  have hinner := interior_mono hint
  rw [interior_interior] at hinner
  have hstrict := (mem_interior_horizontalBand_iff 0 (1 / 2) squareCenter).mp
    (hinner hc)
  norm_num [squareCenter] at hstrict

/-- A top corner supplies the strict interior-height witness needed by
the bottom-side crosscut barrier. -/
theorem exists_interior_above_of_top_corner {P : Set Plane} (hP : IsJordanRegion P)
    {k : Fin 4} (hk : k = 2 ∨ k = 3) (hp : corner k ∈ P) :
    ∃ q ∈ interior P, (1 / 2 : ℝ) < q 1 := by
  apply exists_interior_above_of_mem_height hP hp
  rcases hk with rfl | rfl <;> norm_num [corner]

/-- In the normalized opposite-side configuration, all three pieces other
than the lower cap rise strictly above the midline in their interiors. -/
theorem other_piece_above_midline (d : SquareDissection)
    (hBL : corner 0 ∈ d.piece 0)
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hTR : corner 2 ∈ d.piece 2)
    (hcenter : squareCenter ∈ interior (d.piece 3)) :
    ∀ j : Fin 4, j ≠ 0 → ∃ q ∈ interior (d.piece j), (1 / 2 : ℝ) < q 1 := by
  have hTL : corner 3 ∈ d.piece 1 := by
    rw [← hreflect]
    refine ⟨corner 0, hBL, ?_⟩
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  intro j hj
  fin_cases j
  · exact False.elim (hj rfl)
  · exact exists_interior_above_of_top_corner (d.jordan 1) (Or.inr rfl) hTL
  · exact exists_interior_above_of_top_corner (d.jordan 2) (Or.inl rfl) hTR
  · exact exists_interior_above_of_center (d.piece_subset 3) hcenter

/-- The bottom edge is an actual subset of the lower Jordan piece in the
normalized opposite-side branch. -/
theorem bottom_side_subset (d : SquareDissection)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hheight : ∀ p ∈ d.piece 0, p 1 ≤ (1 / 2 : ℝ))
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hTR : corner 2 ∈ d.piece 2)
    (hcenter : squareCenter ∈ interior (d.piece 3)) :
    segment ℝ (corner 0) (corner 1) ⊆ d.piece 0 := by
  have hBL' : Schoenflies.Plane.mk 0 0 ∈ d.piece 0 := by
    simpa [corner, Schoenflies.Plane.mk] using hBL
  have hBR' : Schoenflies.Plane.mk 1 0 ∈ d.piece 0 := by
    simpa [corner, Schoenflies.Plane.mk] using hBR
  simpa [corner, Schoenflies.Plane.mk] using
    RectangularHull.squareDissection_bottom_side_forced d hBL' hBR' hheight
      (other_piece_above_midline d hBL hreflect hTR hcenter)

/-- Coordinate form of the forced bottom side. -/
theorem bottom_point_mem (d : SquareDissection)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hheight : ∀ p ∈ d.piece 0, p 1 ≤ (1 / 2 : ℝ))
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hTR : corner 2 ∈ d.piece 2)
    (hcenter : squareCenter ∈ interior (d.piece 3))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Schoenflies.Plane.mk t 0 ∈ d.piece 0 := by
  apply bottom_side_subset d hBL hBR hheight hreflect hTR hcenter
  change Schoenflies.Plane.mk t 0 ∈
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0)
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
  exact ⟨rfl, ht⟩

end Puzzling139335.N6.TwoDouble.HorizontalAcute
