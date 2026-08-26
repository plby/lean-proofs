import ErdosProblems.Erdos633b.Barycentric
import Mathlib.Analysis.Convex.Extreme

/-! Symmetric barycentric tests and extreme outer corners, without an
edge-to-edge assumption on a tiling. -/

namespace Erdos633b

namespace Triangle

theorem mem_support_iff_all_coords (T : Triangle) (p : Plane) :
    p ∈ T.support ↔ ∀ i, 0 ≤ T.coord i p := by
  change p ∈ convexHull ℝ (Set.range T.affineBasis) ↔ _
  rw [T.affineBasis.convexHull_eq_nonneg_coord]
  rfl

theorem mem_interior_support_iff_all_coords (T : Triangle) (p : Plane) :
    p ∈ interior T.support ↔ ∀ i, 0 < T.coord i p := by
  change p ∈ interior (convexHull ℝ (Set.range T.affineBasis)) ↔ _
  rw [T.affineBasis.interior_convexHull]
  rfl

theorem coord_nonneg (T : Triangle) {p : Plane} (hp : p ∈ T.support) (i : Fin 3) :
    0 ≤ T.coord i p := (T.mem_support_iff_all_coords p).mp hp i

theorem coord_le_one (T : Triangle) {p : Plane} (hp : p ∈ T.support) (i : Fin 3) :
    T.coord i p ≤ 1 := by
  have hs := T.coord_sum p
  have h0 := T.coord_nonneg hp 0
  have h1 := T.coord_nonneg hp 1
  have h2 := T.coord_nonneg hp 2
  fin_cases i
  · change T.coord 0 p ≤ 1
    linarith
  · change T.coord 1 p ≤ 1
    linarith
  · change T.coord 2 p ≤ 1
    linarith

theorem eq_vertex_of_coord_eq_one (T : Triangle) {p : Plane} (hp : p ∈ T.support)
    (i : Fin 3) (hi : T.coord i p = 1) : p = T.points i := by
  have hs := T.coord_sum p
  have h0 := T.coord_nonneg hp 0
  have h1 := T.coord_nonneg hp 1
  have h2 := T.coord_nonneg hp 2
  apply T.affineBasis.ext_elem
  intro j
  change T.coord j p = T.coord j (T.points i)
  rw [T.coord_vertex]
  fin_cases i
  · change T.coord 0 p = 1 at hi
    fin_cases j
    · exact hi
    · change T.coord 1 p = 0
      linarith
    · change T.coord 2 p = 0
      linarith
  · change T.coord 1 p = 1 at hi
    fin_cases j
    · change T.coord 0 p = 0
      linarith
    · exact hi
    · change T.coord 2 p = 0
      linarith
  · change T.coord 2 p = 1 at hi
    fin_cases j
    · change T.coord 0 p = 0
      linarith
    · change T.coord 1 p = 0
      linarith
    · exact hi

theorem vertex_mem_extremePoints (T : Triangle) (i : Fin 3) :
    T.points i ∈ T.support.extremePoints ℝ := by
  rw [mem_extremePoints_iff_left]
  refine ⟨T.vertex_mem_support i, ?_⟩
  intro x hx y hy hseg
  have hs : (1 : ℝ) ∈ openSegment ℝ (T.coord i x) (T.coord i y) := by
    rw [← image_openSegment ℝ (T.coord i)]
    exact ⟨T.points i, hseg, by simp [coord_vertex]⟩
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hs
  change a * T.coord i x + b * T.coord i y = 1 at heq
  have hx1 := T.coord_le_one hx i
  have hy1 := T.coord_le_one hy i
  apply T.eq_vertex_of_coord_eq_one hx i
  apply le_antisymm hx1
  by_contra h
  have hpos := mul_pos ha (sub_pos.mpr (lt_of_not_ge h))
  have hnonneg := mul_nonneg hb.le (sub_nonneg.mpr hy1)
  nlinarith

/-- An outer vertex cannot be in the relative interior of a smaller
triangle's edge, nor in the smaller triangle's interior. -/
theorem vertex_of_support_subset (T S : Triangle) (hST : S.support ⊆ T.support)
    (i : Fin 3) (hi : T.points i ∈ S.support) :
    ∃ j : Fin 3, S.points j = T.points i := by
  have he : T.points i ∈ S.support.extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset hST
      ⟨hi, T.vertex_mem_extremePoints i⟩
  exact Set.mem_range.mp (extremePoints_convexHull_subset he)

end Triangle

namespace Tiling

theorem outer_vertex_of_mem_piece {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) (k : Fin n) (hk : T.points i ∈ d.place k '' d.tile.support) :
    ∃ j : Fin 3, d.place k (d.tile.points j) = T.points i := by
  let S : Triangle := d.tile.move (d.place k)
  have hs : S.support = d.place k '' d.tile.support :=
    d.tile.support_move (d.place k)
  exact T.vertex_of_support_subset S (by rw [hs]; exact d.piece_subset k) i
    (by rw [hs]; exact hk)

theorem outer_vertex_is_tile_vertex {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) : ∃ k : Fin n, ∃ j : Fin 3,
      d.place k (d.tile.points j) = T.points i := by
  have h := T.vertex_mem_support i
  rw [← d.covers, Set.mem_iUnion] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, d.outer_vertex_of_mem_piece i k hk⟩

end Tiling

end Erdos633b
