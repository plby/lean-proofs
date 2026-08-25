import StackExchange.Puzzling139335.N4OuterPair.Bases
import StackExchange.Puzzling139335.N4OuterPair.Midline
import StackExchange.Puzzling139335.N4OuterPair.AxisBand

/-!
# A middle piece cannot have a horizontal image of the unit base

The full actual frontier segment is a horizontal separator. Weighted mass
forces its height to be an integer quarter. The reflected outer pieces and
the two strict midline contacts force that height strictly between one
quarter and three quarters. The sole remaining height cuts through the
protected center.
-/

open Set

namespace Puzzling139335.N4OuterPair

open PlaneIsometries

namespace Configuration

/-- Every congruence from the bottom outer piece to a middle piece sends
the unit base to a nonhorizontal direction. -/
theorem middle_base_not_horizontal {d : SquareDissection} (h : Configuration d)
    (hc : d.HasProtectedCenter) {i : Fin 4} (hi : i = 2 ∨ i = 3)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece i)
    (hAxis : linearMatrix e 1 0 = 0) : False := by
  have hp0 : (!₂[0, 0] : Plane) ∈ d.piece 0 := h.bottom_left_mk
  have hp1 : (!₂[1, 0] : Plane) ∈ d.piece 0 := h.bottom_right_mk
  have he0 : e !₂[0, 0] ∈ d.piece i := by
    rw [← he]
    exact mem_image_of_mem e hp0
  have he1 : e !₂[1, 0] ∈ d.piece i := by
    rw [← he]
    exact mem_image_of_mem e hp1
  let y : ℝ := (e !₂[0, 0]) 1
  have hy : y ∈ Icc (0 : ℝ) 1 := (d.piece_subset i he0).2
  have hbase_eq : e '' segment ℝ !₂[0, 0] !₂[1, 0] =
      segment ℝ !₂[0, y] !₂[1, y] :=
    horizontal_unit_base_image e (d.piece_subset i he0) (d.piece_subset i he1) hAxis
  have hbase : segment ℝ !₂[0, y] !₂[1, y] ⊆ d.piece i := by
    rw [← hbase_eq]
    exact h.image_base_subset hc he
  have hbase_frontier : segment ℝ !₂[0, y] !₂[1, y] ⊆ frontier (d.piece i) := by
    rw [← hbase_eq]
    exact h.image_base_frontier hc he
  have hy0 : y ≠ 0 := by
    intro hzero
    have hpoint := hbase (left_mem_segment ℝ !₂[0, y] !₂[1, y])
    apply h.middle_cornerless i hi 0
    simpa [corner, hzero, Fin.ext_iff] using hpoint
  have hy1 : y ≠ 1 := by
    intro hone
    have hpoint := hbase (left_mem_segment ℝ !₂[0, y] !₂[1, y])
    apply h.middle_cornerless i hi 3
    simpa [corner, hone, Fin.ext_iff] using hpoint
  have hypos : 0 < y := lt_of_le_of_ne hy.1 hy0.symm
  have hylt : y < 1 := lt_of_le_of_ne hy.2 hy1
  have hfront : {p : Plane | p ∈ unitSquare ∧ p 1 = y} ⊆
      ⋃ j, frontier (d.piece j) := by
    intro p hp
    apply mem_iUnion.mpr
    refine ⟨i, hbase_frontier ?_⟩
    change p ∈ segment ℝ (Schoenflies.Plane.mk 0 y) (Schoenflies.Plane.mk 1 y)
    rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hp.2, hp.1.1⟩
  have havoid := d.interiors_avoid_height_of_horizontal_frontier_cover hfront
  have hbottom : d.piece 0 ⊆ horizontalBand 0 y := by
    apply ((d.jordan 0).subset_horizontalBand_or_of_avoids_height
      (d.piece_subset 0) (havoid 0)).resolve_right
    intro habove
    have hzero := (habove hp0).2.1
    change y ≤ (0 : ℝ) at hzero
    linarith only [hypos, hzero]
  have htop : d.piece 1 ⊆ horizontalBand y 1 := by
    apply ((d.jordan 1).subset_horizontalBand_or_of_avoids_height
      (d.piece_subset 1) (havoid 1)).resolve_left
    intro hbelow
    have hone := (hbelow (h.top_point_mem hc (by norm_num : (0 : ℝ) ∈ Icc 0 1))).2.2
    change (1 : ℝ) ≤ y at hone
    linarith only [hylt, hone]
  have hbottom_reflected : d.piece 0 ⊆ horizontalBand 0 (1 - y) := by
    intro p hp
    have hreflection : ReflectionSeparation.horizontal p ∈ d.piece 1 := by
      rw [← h.reflected]
      exact mem_image_of_mem ReflectionSeparation.horizontal hp
    have hheight := (htop hreflection).2.1
    rw [ReflectionSeparation.horizontal_apply_one] at hheight
    have hpS := d.piece_subset 0 hp
    exact ⟨hpS.1, hpS.2.1, by linarith only [hheight]⟩
  obtain ⟨⟨p, hp, hpy⟩, ⟨q, hq, hqy⟩⟩ := h.middle_crosses_midline hc hi
  have hpimage : p ∈ e '' d.piece 0 := by
    rw [he]
    exact interior_subset hp
  have hqimage : q ∈ e '' d.piece 0 := by
    rw [he]
    exact interior_subset hq
  have hupper := (horizontal_image_band_bounds e hAxis hbottom hqimage).2
  change q 1 ≤ y + y at hupper
  have hlower := (horizontal_image_band_bounds e hAxis hbottom_reflected hpimage).1
  change y - (1 - y) ≤ p 1 at hlower
  have hyquarter : (1 / 4 : ℝ) < y := by linarith only [hupper, hqy]
  have hythreequarters : y < (3 / 4 : ℝ) := by linarith only [hlower, hpy]
  obtain ⟨k, hk, hky⟩ := d.horizontal_frontier_separator_height_eq_nat_quarter hy hfront
  have hklo : (1 : ℝ) < k := by linarith only [hyquarter, hky]
  have hkhi : (k : ℝ) < 3 := by linarith only [hythreequarters, hky]
  have hklo' : 1 < k := by exact_mod_cast hklo
  have hkhi' : k < 3 := by exact_mod_cast hkhi
  have hk2 : k = 2 := by omega
  have hyhalf : y = (1 / 2 : ℝ) := by
    rw [hky, hk2]
    norm_num
  obtain ⟨j, hj⟩ := hc
  exact havoid j squareCenter hj (by simpa only [squareCenter_apply_one] using hyhalf.symm)

end Configuration

end Puzzling139335.N4OuterPair
