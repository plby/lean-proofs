import StackExchange.Puzzling139335.N4TwoOneOne.SourceBounds
import StackExchange.Puzzling139335.N4TwoOneOne.Isometries

/-! Exact contact transport between the two reflected singleton pieces. -/

open Set

namespace Puzzling139335.N4TwoOneOne

theorem vertical_coordinates (x y : ℝ) :
    ReflectionSeparation.vertical (!₂[x, y] : Plane) = !₂[1 - x, y] := by
  ext i
  fin_cases i <;> simp

namespace SourceData

variable {d : SquareDissection} {θ u v : ℝ}

theorem vertical_mem_left_iff (h : SourceData d θ u v) {p : Plane} :
    ReflectionSeparation.vertical p ∈ d.piece 2 ↔ p ∈ d.piece 1 := by
  rw [← h.singleton_reflection]
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact ReflectionSeparation.vertical.injective hqp ▸ hq
  · exact mem_image_of_mem _

theorem left_mem_iff_vertical_mem_right (h : SourceData d θ u v) {p : Plane} :
    p ∈ d.piece 2 ↔ ReflectionSeparation.vertical p ∈ d.piece 1 := by
  simpa only [ReflectionSeparation.vertical_involutive] using
    (h.vertical_mem_left_iff (p := ReflectionSeparation.vertical p))

theorem left_side_mem_iff_right_side_mem (h : SourceData d θ u v) (y : ℝ) :
    (!₂[0, y] : Plane) ∈ d.piece 2 ↔ (!₂[1, y] : Plane) ∈ d.piece 1 := by
  simpa only [vertical_coordinates, sub_zero] using
    (h.left_mem_iff_vertical_mem_right (p := !₂[0, y]))

theorem left_in_left_half (h : SourceData d θ u v) :
    d.piece 2 ⊆ {p : Plane | p 0 ≤ (1 / 2 : ℝ)} := by
  intro p hp
  have hbound := h.right_in_right_half (h.left_mem_iff_vertical_mem_right.mp hp)
  change (1 / 2 : ℝ) ≤ ReflectionSeparation.vertical p 0 at hbound
  rw [ReflectionSeparation.vertical_apply_zero] at hbound
  change p 0 ≤ (1 / 2 : ℝ)
  linarith

theorem left_side_not_right (h : SourceData d θ u v) (y : ℝ) :
    (!₂[0, y] : Plane) ∉ d.piece 1 := by
  intro hp
  have hbound := h.right_in_right_half hp
  norm_num at hbound

theorem right_side_not_left (h : SourceData d θ u v) (y : ℝ) :
    (!₂[1, y] : Plane) ∉ d.piece 2 := by
  intro hp
  have hbound := h.left_in_left_half hp
  norm_num at hbound

/-- Membership in the actual right image pulls back through its isometry. -/
theorem mem_source_of_rightMap_mem (h : SourceData d θ u v) {p : Plane}
    (hp : rightMap θ u v p ∈ d.piece 1) : p ∈ d.piece 0 := by
  obtain ⟨q, hq, hqp⟩ := h.right_image.symm ▸ hp
  exact rightMap_injective θ u v hqp ▸ hq

theorem rightMap_mem_iff (h : SourceData d θ u v) {p : Plane} :
    rightMap θ u v p ∈ d.piece 1 ↔ p ∈ d.piece 0 := by
  refine ⟨h.mem_source_of_rightMap_mem, ?_⟩
  intro hp
  rw [← h.right_image]
  exact mem_image_of_mem _ hp

end SourceData

end Puzzling139335.N4TwoOneOne
