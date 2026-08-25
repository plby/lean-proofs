import StackExchange.Puzzling139335.RectangularHull.NormalizedBands
import StackExchange.Puzzling139335.RectangularHull.HorizontalSeparator
import StackExchange.Puzzling139335.SingletonBand
import StackExchange.Puzzling139335.RectangularHull.ConvexClosure

/-!
# Quarter-height segments force rectangular pieces

A full horizontal segment in either middle piece separates the adjacent
outer piece into a quarter band. The weighted-mass equality then fills that
band, and congruence propagates its convexity to every piece.
-/

open Set

namespace Puzzling139335.RectangularHull

private theorem height_eq_quarter_of_bottom_eq {d : SquareDissection} {h : ℝ}
    (N : NormalizedOuterBands d h)
    (heq : d.piece 0 = horizontalBand 0 (1 / 4)) : h = 1 / 4 := by
  have hconv : Convex ℝ (horizontalBand 0 (1 / 4)) :=
    convex_closedAxisBox 0 1 0 (1 / 4)
  have hHull : axisBox h = horizontalBand 0 (1 / 4) := by
    rw [← N.bottom_hull, heq, hconv.convexHull_eq]
  have hp : (!₂[0, h] : Plane) ∈ axisBox h := by
    change (0 ≤ (0 : ℝ) ∧ 0 ≤ 1) ∧ 0 ≤ h ∧ h ≤ h
    exact ⟨⟨le_rfl, by norm_num⟩, N.height_pos.le, le_rfl⟩
  have hupper : h ≤ 1 / 4 := by
    rw [hHull] at hp
    exact hp.2.2
  have hq : (!₂[0, 1 / 4] : Plane) ∈ horizontalBand 0 (1 / 4) := by
    norm_num [horizontalBand]
  have hlower : 1 / 4 ≤ h := by
    rw [← hHull] at hq
    exact hq.2.2
  exact le_antisymm hupper hlower

private theorem height_eq_quarter_of_top_eq {d : SquareDissection} {h : ℝ}
    (N : NormalizedOuterBands d h)
    (heq : d.piece 1 = horizontalBand (3 / 4) 1) : h = 1 / 4 := by
  have hconv : Convex ℝ (horizontalBand (3 / 4) 1) :=
    convex_closedAxisBox 0 1 (3 / 4) 1
  have hHull : horizontalBand (1 - h) 1 = horizontalBand (3 / 4) 1 := by
    rw [← N.top_hull, heq, hconv.convexHull_eq]
  have hp : (!₂[0, 1 - h] : Plane) ∈ horizontalBand (1 - h) 1 := by
    change (0 ≤ (0 : ℝ) ∧ 0 ≤ 1) ∧ 1 - h ≤ 1 - h ∧ 1 - h ≤ 1
    exact ⟨⟨le_rfl, by norm_num⟩, le_rfl, by linarith [N.height_pos]⟩
  have hupper : 3 / 4 ≤ 1 - h := by
    rw [hHull] at hp
    exact hp.2.1
  have hq : (!₂[0, 3 / 4] : Plane) ∈ horizontalBand (3 / 4) 1 := by
    norm_num [horizontalBand]
  have hlower : 1 - h ≤ 3 / 4 := by
    rw [← hHull] at hq
    exact hq.2.1
  linarith

/-- A horizontal unit segment at a quarter height in a middle piece forces
the normalized outer-band height to be one quarter and every tile to be
convex. -/
theorem quarter_horizontal_segment_forces_height_and_convex
    {d : SquareDissection} {h : ℝ} {k : Fin 4} {y : ℝ}
    (N : NormalizedOuterBands d h) (hk : k = 2 ∨ k = 3)
    (hy : y = 1 / 4 ∨ y = 3 / 4)
    (hseg : segment ℝ (!₂[0, y] : Plane) (!₂[1, y] : Plane) ⊆ d.piece k) :
    h = 1 / 4 ∧ ∀ i, Convex ℝ (d.piece i) := by
  rcases hy with rfl | rfl
  · have h0k : (0 : Fin 4) ≠ k := by
      rcases hk with rfl | rfl <;> decide
    rcases horizontal_segment_separates_pieces d hseg h0k with hbelow | habove
    · have hsub : d.piece 0 ⊆ horizontalBand 0 (1 / 4) := by
        intro p hp
        have hs := d.piece_subset 0 hp
        exact ⟨hs.1, hs.2.1, hbelow p hp⟩
      have heq := d.piece_eq_lower_quarter_band hsub
      have hconv : Convex ℝ (d.piece 0) := by
        rw [heq]
        exact convex_closedAxisBox 0 1 0 (1 / 4)
      exact ⟨height_eq_quarter_of_bottom_eq N heq, d.piece_convex_of_one hconv⟩
    · have hbad := habove (!₂[0, 0] : Plane) N.bottom_corners.1
      norm_num at hbad
  · have h1k : (1 : Fin 4) ≠ k := by
      rcases hk with rfl | rfl <;> decide
    rcases horizontal_segment_separates_pieces d hseg h1k with hbelow | habove
    · have hbad := hbelow (!₂[1, 1] : Plane) N.top_corners.2
      norm_num at hbad
    · have hsub : d.piece 1 ⊆ horizontalBand (3 / 4) 1 := by
        intro p hp
        have hs := d.piece_subset 1 hp
        exact ⟨hs.1, habove p hp, hs.2.2⟩
      have heq := d.piece_eq_upper_quarter_band hsub
      have hconv : Convex ℝ (d.piece 1) := by
        rw [heq]
        exact convex_closedAxisBox 0 1 (3 / 4) 1
      exact ⟨height_eq_quarter_of_top_eq N heq, d.piece_convex_of_one hconv⟩

end Puzzling139335.RectangularHull
