import StackExchange.Puzzling139335.N4TwoOneOne.TopGap
import StackExchange.Puzzling139335.N4OuterPair.AxisBand

/-!
# The fourth piece cannot have a horizontal image base

The fourth piece contains the square center and the top midpoint, so its
vertical span is at least one half. The source has strictly smaller vertical
span. A congruence with horizontal image of the source base preserves vertical
distances, which gives the contradiction directly from actual memberships.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

theorem horizontal_axis_image_false {d : SquareDissection} {θ u v : ℝ}
    (hcfg : Configuration d) (h : SourceData d θ u v) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (hAxis : PlaneIsometries.linearMatrix e 1 0 = 0) : False := by
  obtain ⟨p, hp, hpTop⟩ := he.symm ▸ h.top_midpoint_mem hcfg
  obtain ⟨q, hq, hqCenter⟩ :=
    he.symm ▸ interior_subset (h.center_piece_three hc)
  have hp0 : 0 ≤ p 1 := (d.piece_subset 0 hp).2.1
  have hq0 : 0 ≤ q 1 := (d.piece_subset 0 hq).2.1
  have hpHalf : p 1 < 1 / 2 :=
    h.height_lt_half hcfg.right_vertical_germ (h.angle_lt_half_pi hcfg) hp
  have hqHalf : q 1 < 1 / 2 :=
    h.height_lt_half hcfg.right_vertical_germ (h.angle_lt_half_pi hcfg) hq
  have hpY : (e p) 1 = 1 := by
    rw [hpTop]
    rfl
  have hqY : (e q) 1 = 1 / 2 := by
    rw [hqCenter]
    rfl
  rw [N4OuterPair.horizontal_apply_y e hAxis p] at hpY
  rw [N4OuterPair.horizontal_apply_y e hAxis q] at hqY
  rcases N4OuterPair.horizontal_vertical_coefficient e hAxis with hpos | hneg
  · rw [hpos, one_mul] at hpY hqY
    linarith only [hpY, hqY, hq0, hpHalf]
  · rw [hneg, neg_one_mul] at hpY hqY
    linarith only [hpY, hqY, hp0, hqHalf]

end Puzzling139335.N4TwoOneOne
