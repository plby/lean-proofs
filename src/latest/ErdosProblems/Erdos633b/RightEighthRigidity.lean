import ErdosProblems.Erdos633b.RightEighthMetric
import ErdosProblems.Erdos633b.CornerAngleWeights

/-! A scalene triangle tiled by a pi/8 right triangle is a reptiling,
with no restrictions on the number of pieces or on the outer ordering. -/

namespace Erdos633b.Tiling

theorem right_eighth_reptiling {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hα : d.tile.angle 0 = Real.pi / 8)
    (hscalene : Function.Injective T.angle) : ReptilingAngles d.tile T := by
  have hβ : d.tile.angle 1 = 3 * Real.pi / 8 := by linarith [d.tile.angle_sum]
  obtain ⟨c, hrow, hp, hs⟩ := d.integer_corner_weights 8 (by norm_num) ![1, 3, 4] (by
    intro j
    fin_cases j <;> norm_num
    · change d.tile.angle 0 = Real.pi / 8
      exact hα
    · change d.tile.angle 1 = (3 : ℝ) * (Real.pi / 8)
      linarith [hβ]
    · change d.tile.angle 2 = (4 : ℝ) * (Real.pi / 8)
      linarith [hright])
  norm_num only [Nat.cast_ofNat] at hrow
  obtain ⟨e, h01, h12⟩ := ordered_integer_weights T c _ hrow hscalene
  have heSum : c (e 0) + c (e 1) + c (e 2) = 8 := (sorted_weights_sum c e).trans hs
  rcases sorted_partition_eight _ _ _ (hp (e 0)) h01 h12 heSum with ⟨hc0, hc1, hc2⟩ |
    ⟨hc0, hc1, hc2⟩
  · exfalso
    let d' := d.reindexOuter e.symm
    have hU (i : Fin 3) : Triangle.angle (T.reindex e.symm) i = (c (e i) : ℝ) * (Real.pi / 8) := by
      simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hrow (e i)
    apply d'.right_eighth_ordered_impossible hright hα
    · simpa only [hc0, Nat.cast_one, one_mul] using hU 0
    · have h := hU 1
      rw [hc1] at h
      norm_num at h
      linarith
    · have h := hU 2
      rw [hc2] at h
      norm_num at h
      linarith
  · apply reptilingAngles_of_two_matched_angles d.tile T (e 0) (e 2) 0 2
      (fun h => (by decide : (0 : Fin 3) ≠ 2) (e.injective h)) (by decide)
    · rw [hrow, hc0, Nat.cast_one, one_mul, hα]
    · rw [hrow, hc2, hright]
      norm_num
      ring

end Erdos633b.Tiling
