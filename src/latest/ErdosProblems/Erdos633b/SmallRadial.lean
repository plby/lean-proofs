import ErdosProblems.Erdos633b.CornerCoordinates

/-! Positive radial points in arbitrary open corner neighborhoods. -/

namespace Erdos633b

theorem exists_small_radial (O q : Plane) {U : Set Plane} (hU : IsOpen U) (hO : O ∈ U) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ AffineMap.homothety O r q ∈ U := by
  let L : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap O q
  have hL : Continuous L := L.continuous_of_finiteDimensional
  have hz : (0 : ℝ) ∈ L ⁻¹' U := by simpa [L] using hO
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp (hU.preimage hL) 0 hz
  let r : ℝ := min ε 1 / 2
  have hr : 0 < r := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have hre : r < ε := by
    have hm := min_le_left ε (1 : ℝ)
    dsimp [r]
    linarith
  have hr1 : r < 1 := by
    have hm := min_le_right ε (1 : ℝ)
    dsimp [r]
    linarith
  refine ⟨r, hr, hr1, ?_⟩
  have hrb : r ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr]
    exact hre
  exact (AffineMap.homothety_eq_lineMap O r q).symm ▸ hb hrb

namespace Triangle

theorem homothety_vertex_mem_support (T : Triangle) (i : Fin 3) {q : Plane}
    (hq : q ∈ T.support) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    AffineMap.homothety (T.points i) r q ∈ T.support := by
  rw [AffineMap.homothety_eq_lineMap]
  exact T.support_convex.segment_subset (T.vertex_mem_support i) hq
    (lineMap_mem_segment ℝ _ _ ⟨hr, hr1⟩)

theorem coord_radial_shared (T S : Triangle) (i j k : Fin 3)
    (hO : S.points j = T.points i) (hk : k ≠ j) (r : ℝ) (q : Plane) :
    S.coord k (AffineMap.homothety (T.points i) r q) = r * S.coord k q := by
  rw [← hO, S.coord_homothety_vertex, S.coord_vertex, if_neg hk, sub_zero, add_zero]

theorem radial_mem_interior_of_noncentral_pos (S : Triangle) (j : Fin 3) (r : ℝ)
    (hr : 0 < r) (q : Plane) (h1 : 0 < S.coord (j + 1) q) (h2 : 0 < S.coord (j + 2) q)
    (hj : 0 < S.coord j (AffineMap.homothety (S.points j) r q)) :
    AffineMap.homothety (S.points j) r q ∈ interior S.support := by
  apply (S.mem_interior_support_iff_all_coords _).mpr
  intro k
  have hk := (by decide : ∀ j k : Fin 3, k = j ∨ k = j + 1 ∨ k = j + 2) j k
  rcases hk with hk | hk | hk
  · simpa only [hk] using hj
  · rw [hk, S.coord_radial_shared S j j (j + 1) rfl
      ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j)]
    exact mul_pos hr h1
  · rw [hk, S.coord_radial_shared S j j (j + 2) rfl
      ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j)]
    exact mul_pos hr h2

end Triangle

end Erdos633b
