import StackExchange.Puzzling139335.N4TwoOneOne.Configuration
import StackExchange.Puzzling139335.N4TwoOneOne.SourceBounds
import StackExchange.Puzzling139335.N4TwoOneOne.Isometries
import StackExchange.Puzzling139335.RectangularHull.HeightBarrier

/-!
# The strict angle and the top middle contact

The endpoint angle would put a bottom contact in an upper singleton, against
the source's height barrier. In the remaining range, a positive source germ
forces every singleton top contact strictly into its own half of the top side.
The top midpoint consequently has a relative neighborhood in the fourth piece.
-/

open Set Metric

namespace Puzzling139335.N4TwoOneOne

namespace SourceData

variable {d : SquareDissection} {θ u v : ℝ}

theorem sourceCorner_mem (h : SourceData d θ u v) :
    sourceCorner θ u v ∈ d.piece 0 := by
  obtain ⟨p, hp, hpc⟩ := h.right_image.symm ▸ h.top_right
  have heq : p = sourceCorner θ u v :=
    rightMap_injective θ u v (hpc.trans (rightMap_sourceCorner θ u v).symm)
  exact heq ▸ hp

theorem angle_lt_half_pi (h : SourceData d θ u v) (hcfg : Configuration d) :
    θ < Real.pi / 2 := by
  by_contra hlt
  have heq : θ = Real.pi / 2 := le_antisymm h.angle_le_half_pi (le_of_not_gt hlt)
  have hu0 : 0 < u := by
    simpa only [heq, Real.cos_pi_div_two] using
      h.cos_lt_u_of_germ hcfg.right_vertical_germ
  have hv0 : v = 0 := by
    have hv := h.v_le_one_sub_sin
    rw [heq, Real.sin_pi_div_two] at hv
    linarith [h.v_nonneg]
  have hbottom : Schoenflies.Plane.mk (1 - u) 0 ∈ d.piece 1 := by
    have hp : rightMap θ u v (corner 1) ∈ d.piece 1 := by
      rw [← h.right_image]
      exact mem_image_of_mem _ h.bottom_right
    simpa [heq, hv0, rightMap, eCoord, fCoord, corner, Schoenflies.Plane.mk] using hp
  apply RectangularHull.bottom_contact_above_height_impossible
    (d.jordan 0) (d.jordan 1) (d.piece_subset 0) (d.piece_subset 1)
    (d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 1))
    (by simpa [corner, Schoenflies.Plane.mk] using h.bottom_left)
    (by simpa [corner, Schoenflies.Plane.mk] using h.bottom_right)
    (fun p hp => h.height_le_half hp)
    ⟨corner 2, h.top_right, by norm_num [corner]⟩
    (by linarith [h.u_le_half]) (by linarith) hbottom

theorem cos_pos (h : SourceData d θ u v) (hcfg : Configuration d) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [h.angle_nonneg, Real.pi_pos], h.angle_lt_half_pi hcfg⟩

theorem v_pos (h : SourceData d θ u v) (hcfg : Configuration d) : 0 < v := by
  obtain ⟨t, ht, hmem⟩ := hcfg.left_vertical_germ
  have hp := (h.projection_bounds hmem).2
  simp only [fCoord, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero,
    zero_add] at hp
  exact (mul_pos (h.cos_pos hcfg) ht).trans_le hp

/-- A top contact of the right singleton is strictly to the right of the
square midline. This uses the actual source germ, not a hull-face length. -/
theorem right_top_contact_gt_half (h : SourceData d θ u v) (hcfg : Configuration d)
    {p : Plane} (hp : p ∈ d.piece 1) (hpy : p 1 = 1) : 1 / 2 < p 0 := by
  obtain ⟨q, hq, rfl⟩ := h.right_image.symm ▸ hp
  have hqs := d.piece_subset 0 hq
  have hf : fCoord θ q = v := by
    change 1 - v + fCoord θ q = 1 at hpy
    linarith
  have hqy : 0 < q 1 := by
    have hn : 0 ≤ Real.sin θ * q 0 := mul_nonneg h.sin_nonneg hqs.1.1
    have hcv : 0 < Real.cos θ * q 1 := by
      dsimp [fCoord] at hf
      linarith [h.v_pos hcfg]
    exact pos_of_mul_pos_right hcv (h.cos_pos hcfg).le
  have he : 0 < eCoord θ q := by
    have hcq : 0 ≤ Real.cos θ * q 0 := mul_nonneg h.cos_nonneg hqs.1.1
    have hsq : 0 < Real.sin θ * q 1 := mul_pos h.sin_pos hqy
    dsimp [eCoord]
    linarith
  change (1 / 2 : ℝ) < 1 - u + eCoord θ q
  linarith [h.u_le_half]

theorem left_top_contact_lt_half (h : SourceData d θ u v) (hcfg : Configuration d)
    {p : Plane} (hp : p ∈ d.piece 2) (hpy : p 1 = 1) : p 0 < 1 / 2 := by
  obtain ⟨q, hq, rfl⟩ := h.singleton_reflection.symm ▸ hp
  have hqy : q 1 = 1 := by simpa only [ReflectionSeparation.vertical_apply_one] using hpy
  have hqhalf := h.right_top_contact_gt_half hcfg hq hqy
  rw [ReflectionSeparation.vertical_apply_zero]
  linarith

theorem top_midpoint_unique (h : SourceData d θ u v) (hcfg : Configuration d) :
    ∀ j : Fin 4, j ≠ 3 → (!₂[(1 / 2 : ℝ), 1] : Plane) ∉ d.piece j := by
  intro j hj hmem
  fin_cases j
  · have hb := h.height_le_half hmem
    norm_num at hb
  · have hb := h.right_top_contact_gt_half hcfg hmem rfl
    norm_num at hb
  · have hb := h.left_top_contact_lt_half hcfg hmem rfl
    norm_num at hb
  · exact hj rfl

theorem top_midpoint_mem (h : SourceData d θ u v) (hcfg : Configuration d) :
    (!₂[(1 / 2 : ℝ), 1] : Plane) ∈ d.piece 3 := by
  obtain ⟨j, hj⟩ := d.exists_piece_mem
    (show (!₂[(1 / 2 : ℝ), 1] : Plane) ∈ unitSquare by norm_num [unitSquare])
  by_cases hj3 : j = 3
  · simpa only [hj3] using hj
  · exact (h.top_midpoint_unique hcfg j hj3 hj).elim

theorem top_midpoint_relative_neighborhood (h : SourceData d θ u v)
    (hcfg : Configuration d) :
    ∃ ε : ℝ, 0 < ε ∧
      ball (!₂[(1 / 2 : ℝ), 1] : Plane) ε ∩ unitSquare ⊆ d.piece 3 :=
  d.unique_piece_relative_neighborhood 3 (h.top_midpoint_unique hcfg)

end SourceData

end Puzzling139335.N4TwoOneOne
