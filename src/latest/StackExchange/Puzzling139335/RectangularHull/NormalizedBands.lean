import StackExchange.Puzzling139335.RectangularHull.AxisBox
import StackExchange.Puzzling139335.RectangularHull.SideContact
import StackExchange.Puzzling139335.RectangularHull.FullSide

/-!
# The normalized opposite outer bands

This structure records geometric conclusions of the rectangular-hull
reduction. It is not part of `SquareDissection`; later reduction lemmas
construct it from the original hypotheses.
-/

open Set

namespace Puzzling139335.RectangularHull

structure NormalizedOuterBands (d : SquareDissection) (h : ℝ) : Prop where
  height_pos : 0 < h
  height_le_half : h ≤ 1 / 2
  bottom_hull : convexHull ℝ (d.piece 0) = axisBox h
  top_hull : convexHull ℝ (d.piece 1) = horizontalBand (1 - h) 1
  middle_cornerless : ∀ i : Fin 4, i = 2 ∨ i = 3 → ∀ j : Fin 4, corner j ∉ d.piece i

theorem axis_box_vertices_mem_of_hull {P : Set Plane} {l r b t : ℝ}
    (hlr : l ≤ r) (hbt : b ≤ t) (hHull : convexHull ℝ P = closedAxisBox l r b t) :
    axisBoxVertices l r b t ⊆ P := by
  intro p hp
  apply extremePoints_convexHull_subset (𝕜 := ℝ)
  rw [hHull]
  exact axisBoxVertices_subset_extremePoints hlr hbt hp

namespace NormalizedOuterBands

variable {d : SquareDissection} {h : ℝ} (N : NormalizedOuterBands d h)

include N

theorem bottom_subset : d.piece 0 ⊆ horizontalBand 0 h := by
  have hsub : d.piece 0 ⊆ convexHull ℝ (d.piece 0) := subset_convexHull ℝ _
  rw [N.bottom_hull] at hsub
  exact hsub

theorem top_subset : d.piece 1 ⊆ horizontalBand (1 - h) 1 := by
  rw [← N.top_hull]
  exact subset_convexHull ℝ _

theorem bottom_corners : (!₂[0, 0] : Plane) ∈ d.piece 0 ∧
    (!₂[1, 0] : Plane) ∈ d.piece 0 := by
  have hv := axis_box_vertices_mem_of_hull (P := d.piece 0)
    (by norm_num : (0 : ℝ) ≤ 1) N.height_pos.le N.bottom_hull
  constructor <;> apply hv <;> simp [axisBoxVertices]

theorem top_corners : (!₂[0, 1] : Plane) ∈ d.piece 1 ∧
    (!₂[1, 1] : Plane) ∈ d.piece 1 := by
  have hh : 1 - h ≤ 1 := by linarith [N.height_pos]
  have hv := axis_box_vertices_mem_of_hull (P := d.piece 1)
    (by norm_num : (0 : ℝ) ≤ 1) hh N.top_hull
  constructor <;> apply hv <;> simp [axisBoxVertices]

theorem bottom_side (hc : d.HasProtectedCenter) :
    segment ℝ (!₂[0, 0] : Plane) (!₂[1, 0] : Plane) ⊆ d.piece 0 :=
  lower_outer_hull_contains_bottom_side d hc N.height_le_half
    N.bottom_corners.1 N.bottom_corners.2 N.bottom_subset

theorem bottom_side_frontier (hc : d.HasProtectedCenter) :
    segment ℝ (!₂[0, 0] : Plane) (!₂[1, 0] : Plane) ⊆ frontier (d.piece 0) := by
  intro p hp
  have hpP := N.bottom_side hc hp
  refine ⟨subset_closure hpP, ?_⟩
  intro hint
  have hm := (mem_interior_horizontalBand_iff 0 h p).mp
    (interior_mono N.bottom_subset hint)
  have hy : p 1 = 0 := by
    rcases hp with ⟨a, b, _, _, _, heq⟩
    have hcoord := congrArg (fun z : Plane => z 1) heq
    simpa using hcoord.symm
  linarith [hm.2.1]

theorem isometry_hull_image {i : Fin 4} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece i) :
    e '' axisBox h = convexHull ℝ (d.piece i) := by
  rw [← N.bottom_hull]
  calc
    e '' convexHull ℝ (d.piece 0) = convexHull ℝ (e '' d.piece 0) :=
      e.toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ (d.piece i) := by rw [he]

theorem isometry_hull_subset_square {i : Fin 4} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece i) : e '' axisBox h ⊆ unitSquare := by
  rw [N.isometry_hull_image e he]
  exact convexHull_min (d.piece_subset i) convex_unitSquare

theorem isometry_base_frontier (hc : d.HasProtectedCenter) {i : Fin 4}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece i) :
    e '' segment ℝ (!₂[0, 0] : Plane) (!₂[1, 0] : Plane) ⊆ frontier (d.piece i) := by
  have himg := image_mono (N.bottom_side_frontier hc) (f := (e : Plane → Plane))
  have hfront : e '' frontier (d.piece 0) = frontier (d.piece i) := by
    calc
      e '' frontier (d.piece 0) = frontier (e '' d.piece 0) :=
        e.toHomeomorph.image_frontier _
      _ = frontier (d.piece i) := by rw [he]
  rw [hfront] at himg
  exact himg

end NormalizedOuterBands

end Puzzling139335.RectangularHull
