import StackExchange.Puzzling139335.AcuteCorner
import StackExchange.Puzzling139335.ThreeCorners.FullCorners

/-!
# Symmetries fix the unique acute endpoint

A full square-corner neighborhood cannot lie in a forty-five-degree cone.
For an actual tile containing the bottom side's two endpoints, this excludes
the full endpoint from the set of acute support points.  The other endpoint
is consequently fixed by every Euclidean symmetry of the tile.
-/

open Set Metric

namespace Puzzling139335.N5

open AcuteCorner

/-- A full relative square neighborhood contains two perpendicular short
rays, which violate the pair bound for a forty-five-degree supporting cone.
This statement requires no Jordan-region hypothesis. -/
theorem not_supports45_of_fullCorner {P : Set Plane} {v : Plane}
    (hfull : UnitPairs.IsFullSquareCorner P v) : ¬ Supports45 P v := by
  intro hacute
  obtain ⟨f, hfv, _, ε, hε, hnear⟩ := hfull.exists_normalized
  have hacute' : Supports45 (f '' P) 0 := by
    simpa only [hfv] using hacute.image f
  let t := min (ε / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hx : dist (!₂[t, 0] : Plane) 0 = t := by
    apply (sq_eq_sq₀ dist_nonneg ht.le).mp
    rw [plane_dist_sq]
    simp
  have hy : dist (!₂[0, t] : Plane) 0 = t := by
    apply (sq_eq_sq₀ dist_nonneg ht.le).mp
    rw [plane_dist_sq]
    simp
  have hpx : (!₂[t, 0] : Plane) ∈ f '' P := by
    apply hnear
    refine ⟨mem_ball.mpr (by rw [hx]; exact htε), ?_⟩
    simpa [unitSquare] using And.intro ht.le ht1
  have hpy : (!₂[0, t] : Plane) ∈ f '' P := by
    apply hnear
    refine ⟨mem_ball.mpr (by rw [hy]; exact htε), ?_⟩
    simpa [unitSquare] using And.intro ht.le ht1
  have hbound := hacute'.pair_bound hpx hpy
  simp only [sub_zero, det, dot, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_zero, zero_mul, sub_zero, add_zero] at hbound
  have hpos : 0 < t * t := mul_pos ht ht
  rw [abs_of_pos hpos] at hbound
  exact (not_le_of_gt hpos) hbound

/-- If the right endpoint of an actual tile's bottom side is full, every
forty-five-degree support point belonging to that tile is its left endpoint. -/
theorem support45_eq_corner_zero (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4)
    (h0 : corner 0 ∈ d.piece i) (h1 : corner 1 ∈ d.piece i)
    (hfull : UnitPairs.IsFullSquareCorner (d.piece i) (corner 1))
    {v : Plane} (hv : v ∈ d.piece i) (hv45 : Supports45 (d.piece i) v) :
    v = corner 0 := by
  rcases d.support45_eq_of_two_corners hc i 0 1 (by decide) h0 h1 hv hv45 with h | h
  · exact h
  · exact (not_supports45_of_fullCorner hfull (h ▸ hv45)).elim

/-- Every actual affine Euclidean symmetry fixes the unique acute endpoint. -/
theorem symmetry_fixes_corner_zero (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4)
    (h0 : corner 0 ∈ d.piece i) (h1 : corner 1 ∈ d.piece i)
    (hfull : UnitPairs.IsFullSquareCorner (d.piece i) (corner 1))
    (h45 : Supports45 (d.piece i) (corner 0))
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : g '' d.piece i = d.piece i) :
    g (corner 0) = corner 0 := by
  have hmem : g (corner 0) ∈ d.piece i := hg ▸ mem_image_of_mem g h0
  have hsupport : Supports45 (d.piece i) (g (corner 0)) := by
    simpa only [hg] using h45.image g
  exact support45_eq_corner_zero d hc i h0 h1 hfull hmem hsupport

end Puzzling139335.N5
