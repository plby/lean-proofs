import StackExchange.Puzzling139335.N4TwoOneOne.Defs
import StackExchange.Puzzling139335.SquareSymmetry.Dissection
import StackExchange.Puzzling139335.SquareSymmetry.CornerPermutation
import StackExchange.Puzzling139335.ThreeCorners.FullCorners

/-!
# Actual normalized corner incidences

This configuration records only actual corner memberships and the reflection
between the two singleton pieces. Its unique corner neighborhoods and third
intrinsic corner are proved below rather than included as scalar assumptions.
-/

open Set Metric

namespace Puzzling139335.N4TwoOneOne

/-- The bottom piece owns two corners, the reflected upper pieces one each,
and the fourth piece has no square corner. -/
structure Configuration (d : SquareDissection) : Prop where
  bottom_left : corner 0 ∈ d.piece 0
  bottom_right : corner 1 ∈ d.piece 0
  top_right : corner 2 ∈ d.piece 1
  top_left : corner 3 ∈ d.piece 2
  right_singleton : ∀ k : Fin 4, corner k ∈ d.piece 1 → k = 2
  left_singleton : ∀ k : Fin 4, corner k ∈ d.piece 2 → k = 3
  cornerless : ∀ k : Fin 4, corner k ∉ d.piece 3
  reflected : ReflectionSeparation.vertical '' d.piece 1 = d.piece 2

namespace Configuration

variable {d : SquareDissection}

theorem bottom_corner_unique (h : Configuration d) {a : Fin 4}
    (ha : a = 0 ∨ a = 1) :
    ∀ j : Fin 4, j ≠ 0 → corner a ∉ d.piece j := by
  intro j hj hamem
  fin_cases j
  · exact hj rfl
  · have heq := h.right_singleton a hamem
    rcases ha with rfl | rfl <;> omega
  · have heq := h.left_singleton a hamem
    rcases ha with rfl | rfl <;> omega
  · exact h.cornerless a hamem

theorem bottom_corner_full (h : Configuration d) {a : Fin 4}
    (ha : a = 0 ∨ a = 1) : UnitPairs.IsFullSquareCorner (d.piece 0) (corner a) := by
  obtain ⟨ε, hε, hnear⟩ :=
    d.unique_piece_relative_neighborhood 0 (h.bottom_corner_unique ha)
  refine ⟨AffineIsometryEquiv.refl ℝ Plane, a, ε, hε, ?_, rfl, ?_⟩
  · simpa using d.piece_subset 0
  · simpa using hnear

/-- A singleton placement cannot send either bottom corner to its upper
corner: that would preserve the whole square and carry the other corner too. -/
theorem singleton_preimage_ne_bottom (h : Configuration d)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 1)
    {a : Fin 4} (ha : a = 0 ∨ a = 1) : e.symm (corner 2) ≠ corner a := by
  intro hpre
  have hea : e (corner a) = corner 2 := by
    rw [← hpre, e.apply_symm_apply]
  have hS := d.unique_corner_congruence_preserves_square 0 1 a 2 e he hea
    (h.bottom_corner_unique ha)
  obtain ⟨σ, hσ⟩ := SquareSymmetry.exists_corner_permutation_of_preserves_square e hS
  have hzero : corner (σ 0) ∈ d.piece 1 := by
    rw [← hσ, ← he]
    exact mem_image_of_mem e h.bottom_left
  have hone : corner (σ 1) ∈ d.piece 1 := by
    rw [← hσ, ← he]
    exact mem_image_of_mem e h.bottom_right
  have hsame : σ 0 = σ 1 := (h.right_singleton _ hzero).trans
    (h.right_singleton _ hone).symm
  exact (by decide : (0 : Fin 4) ≠ 1) (σ.injective hsame)

theorem singleton_preimage_mem (h : Configuration d)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 1) :
    e.symm (corner 2) ∈ d.piece 0 := by
  obtain ⟨p, hp, hpc⟩ := he.symm ▸ h.top_right
  simpa only [← hpc, e.symm_apply_apply] using hp

theorem top_right_unique (h : Configuration d) (hc : d.HasProtectedCenter) :
    ∀ j : Fin 4, j ≠ 1 → corner 2 ∉ d.piece j := by
  intro j hj hmem
  fin_cases j
  · exact d.no_opposite_corners hc 0 0 ⟨h.bottom_left, hmem⟩
  · exact hj rfl
  · have heq := h.left_singleton 2 hmem
    omega
  · exact h.cornerless 2 hmem

/-- The third intrinsic point is also an actual full square corner of the
source, witnessed by the right singleton congruence. -/
theorem singleton_preimage_full (h : Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 1) :
    UnitPairs.IsFullSquareCorner (d.piece 0) (e.symm (corner 2)) := by
  obtain ⟨ε, hε, hnear⟩ := d.unique_piece_relative_neighborhood 1
    (h.top_right_unique hc)
  refine ⟨e, 2, ε, hε, ?_, e.apply_symm_apply _, ?_⟩
  · rw [he]
    exact d.piece_subset 1
  · simpa only [he] using hnear

/-- Unique ownership gives a genuine positive vertical source germ at
either bottom corner, without any boundary smoothness hypothesis. -/
theorem bottom_vertical_germ (h : Configuration d) {a : Fin 4}
    (ha : a = 0 ∨ a = 1) :
    ∃ t : ℝ, 0 < t ∧ !₂[corner a 0, t] ∈ d.piece 0 := by
  obtain ⟨ε, hε, hnear⟩ :=
    d.unique_piece_relative_neighborhood 0 (h.bottom_corner_unique ha)
  let t := min (ε / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hay : corner a 1 = 0 := by
    rcases ha with rfl | rfl <;> norm_num [corner, Fin.ext_iff]
  have hdist : dist (!₂[corner a 0, t] : Plane) (corner a) ^ 2 = t ^ 2 := by
    rw [plane_dist_sq]
    simp [hay]
  have hball : !₂[corner a 0, t] ∈ ball (corner a) ε := by
    apply mem_ball.mpr
    have hdnonneg := dist_nonneg (x := (!₂[corner a 0, t] : Plane)) (y := corner a)
    nlinarith [sq_nonneg (ε - t)]
  refine ⟨t, ht, hnear ⟨hball, ?_⟩⟩
  exact ⟨(corner_mem_unitSquare a).1, ht.le, ht1⟩

theorem left_vertical_germ (h : Configuration d) :
    ∃ t : ℝ, 0 < t ∧ !₂[0, t] ∈ d.piece 0 := by
  simpa [corner, Fin.ext_iff] using h.bottom_vertical_germ (Or.inl rfl)

theorem right_vertical_germ (h : Configuration d) :
    ∃ t : ℝ, 0 < t ∧ !₂[1, t] ∈ d.piece 0 := by
  simpa [corner, Fin.ext_iff] using h.bottom_vertical_germ (Or.inr rfl)

end Configuration

end Puzzling139335.N4TwoOneOne
