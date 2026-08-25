import StackExchange.Puzzling139335.N4OuterPair.Defs

/-!
# Actual unit bases and their frontiers in all four copies

The full bottom side is derived from the outer-pair hypotheses.  Square
containment makes it an actual frontier segment, and an arbitrary congruence
then transports it to any piece of the dissection.
-/

open Set

namespace Puzzling139335.N4OuterPair

namespace Configuration

variable {d : SquareDissection}

theorem bottom_point_mem (h : Configuration d) (hc : d.HasProtectedCenter)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Schoenflies.Plane.mk t 0 ∈ d.piece 0 := by
  apply h.bottom_side hc
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  exact ⟨rfl, ht⟩

theorem top_point_mem (h : Configuration d) (hc : d.HasProtectedCenter)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Schoenflies.Plane.mk t 1 ∈ d.piece 1 := by
  apply h.top_side hc
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  exact ⟨rfl, ht⟩

theorem base_frontier (h : Configuration d) (hc : d.HasProtectedCenter) :
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆
      frontier (d.piece 0) := by
  intro p hp
  refine ⟨subset_closure (h.bottom_side hc hp), ?_⟩
  intro hint
  have hfront := RectangularHull.bottom_segment_subset_frontier
    (by norm_num) (by norm_num) (by norm_num) hp
  exact hfront.2 (interior_mono (d.piece_subset 0) hint)

theorem image_base_subset (h : Configuration d) (hc : d.HasProtectedCenter)
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {i : Fin 4} (he : e '' d.piece 0 = d.piece i) :
    e '' segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆ d.piece i := by
  rw [← he]
  exact image_mono (h.bottom_side hc)

theorem image_base_frontier (h : Configuration d) (hc : d.HasProtectedCenter)
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {i : Fin 4} (he : e '' d.piece 0 = d.piece i) :
    e '' segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆
      frontier (d.piece i) := by
  have hf : e '' frontier (d.piece 0) = frontier (d.piece i) := by
    have hf' : e '' frontier (d.piece 0) = frontier (e '' d.piece 0) :=
      e.toHomeomorph.image_frontier (d.piece 0)
    exact hf'.trans (congrArg frontier he)
  rw [← hf]
  exact image_mono (h.base_frontier hc)

theorem segment_image_base_frontier (h : Configuration d) (hc : d.HasProtectedCenter)
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {i : Fin 4} (he : e '' d.piece 0 = d.piece i) :
    segment ℝ (e (Schoenflies.Plane.mk 0 0)) (e (Schoenflies.Plane.mk 1 0)) ⊆
      frontier (d.piece i) := by
  have himage : e '' segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) =
      segment ℝ (e (Schoenflies.Plane.mk 0 0)) (e (Schoenflies.Plane.mk 1 0)) :=
    image_segment ℝ e.toAffineEquiv.toAffineMap _ _
  rw [← himage]
  exact h.image_base_frontier hc he

/-- Every actual piece has a congruent image of the full unit base in its frontier. -/
theorem exists_unit_base_frontier (h : Configuration d) (hc : d.HasProtectedCenter)
    (i : Fin 4) :
    ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, e '' d.piece 0 = d.piece i ∧
      segment ℝ (e (Schoenflies.Plane.mk 0 0)) (e (Schoenflies.Plane.mk 1 0)) ⊆
        frontier (d.piece i) := by
  obtain ⟨e, he⟩ := d.congruent 0 i
  exact ⟨e, he, h.segment_image_base_frontier hc he⟩

end Configuration

end Puzzling139335.N4OuterPair
