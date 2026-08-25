import StackExchange.Puzzling139335.N5.Normalization
import StackExchange.Puzzling139335.N5.BottomSide
import StackExchange.Puzzling139335.N5.CornerFrame
import StackExchange.Puzzling139335.N5.Transport

/-!
# The actual normalized configuration for five corner incidences

All fields record physical memberships, corner counts, or an equality
under the fixed diagonal reflection.  They contain no assumed angles,
supporting-face lengths, or convex-hull conclusions.
-/

open Set

namespace Puzzling139335.N5

structure Normalized (d : SquareDissection) : Prop where
  count_zero : d.tileCornerCount 0 = 2
  count_one : d.tileCornerCount 1 = 2
  count_two : d.tileCornerCount 2 = 1
  count_three : d.tileCornerCount 3 = 0
  bottom_left : corner 0 ∈ d.piece 0
  bottom_right : corner 1 ∈ d.piece 0
  diagonal_image : ReflectionSeparation.diagonal '' d.piece 0 = d.piece 1
  top_right : corner 2 ∈ d.piece 2

theorem Normalized.incidence_count {d : SquareDissection} (h : Normalized d) :
    d.cornerIncidenceCount = 5 := by
  rw [d.cornerIncidenceCount_eq_sum_tileCornerCount, CornerCounting.sum_fin_four,
    h.count_zero, h.count_one, h.count_two, h.count_three]

theorem Normalized.left_bottom {d : SquareDissection} (h : Normalized d) :
    corner 0 ∈ d.piece 1 := by
  have hzero : ReflectionSeparation.diagonal (corner 0) = corner 0 := by
    apply ReflectionSeparation.diagonal_fixed
    norm_num [corner, Fin.ext_iff]
  have hmem := mem_image_of_mem ReflectionSeparation.diagonal h.bottom_left
  rwa [h.diagonal_image, hzero] at hmem

theorem Normalized.split_count {d : SquareDissection} (h : Normalized d) :
    d.cornerTileCount 0 = 2 :=
  count_two_of_two_owners d h.incidence_count (by decide : (0 : Fin 4) ≠ 1)
    h.bottom_left h.left_bottom

theorem Normalized.unique_top_right {d : SquareDissection} (h : Normalized d) :
    ∀ k, k ≠ 2 → corner 2 ∉ d.piece k :=
  unique_corner_of_count_one d
    (count_one_of_ne_split d h.incidence_count h.split_count (by decide)) h.top_right

theorem Normalized.below_diagonal {d : SquareDissection} (h : Normalized d) :
    d.piece 0 ⊆ {p | p 1 ≤ p 0} :=
  ReflectionSeparation.diagonal_below_of_bottom_right (d.jordan 0) h.diagonal_image
    (d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 1)) h.bottom_right

theorem Normalized.bottom_left_sides {d : SquareDissection} (h : Normalized d) :
    segment ℝ (corner 0) (corner 1) ⊆ d.piece 0 ∧
      segment ℝ (corner 0) (corner 3) ⊆ d.piece 1 :=
  bottom_left_segments_subset_of_diagonal_pair d
    (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 2)
    (by decide : (1 : Fin 4) ≠ 2)
    h.bottom_left h.bottom_right h.top_right h.diagonal_image

theorem Normalized.center_not_mem_pair {d : SquareDissection} (h : Normalized d) :
    squareCenter ∉ interior (d.piece 0) ∧ squareCenter ∉ interior (d.piece 1) :=
  d.center_not_mem_fixed_pair (by decide : (0 : Fin 4) ≠ 1)
    ReflectionSeparation.diagonal h.diagonal_image ReflectionSeparation.diagonal_center

theorem Normalized.center_owner_cases {d : SquareDissection} (h : Normalized d)
    {i : Fin 4} (hi : squareCenter ∈ interior (d.piece i)) : i = 2 ∨ i = 3 := by
  fin_cases i
  · exact (h.center_not_mem_pair.1 hi).elim
  · exact (h.center_not_mem_pair.2 hi).elim
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- In any actual placement of the bottom piece into the singleton-corner
piece, the preimage of the top-right corner is a third point of the
prototype, distinct from its two bottom endpoints. -/
theorem Normalized.third_corner_preimage {d : SquareDissection} (h : Normalized d)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2) :
    e.symm (corner 2) ∈ d.piece 0 ∧
      e.symm (corner 2) ≠ corner 0 ∧ e.symm (corner 2) ≠ corner 1 := by
  have hcount : d.tileCornerCount 0 ≠ d.tileCornerCount 2 := by
    rw [h.count_zero, h.count_two]
    decide
  refine ⟨?_, preimage_unique_corner_not_corner d e he h.unique_top_right hcount 0,
    preimage_unique_corner_not_corner d e he h.unique_top_right hcount 1⟩
  obtain ⟨x, hx, hxe⟩ := he.symm ▸ h.top_right
  have hxpre : x = e.symm (corner 2) := by
    rw [← hxe, e.symm_apply_apply]
  exact hxpre ▸ hx

end Puzzling139335.N5
