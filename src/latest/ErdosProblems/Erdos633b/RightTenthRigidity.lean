import ErdosProblems.Erdos633b.RightTenthMetric
import ErdosProblems.Erdos633b.CornerAngleWeights

/-! A scalene triangle tiled by a pi/10 right triangle must be similar
to that tile. All finite positive weight partitions are covered. -/

namespace Erdos633b.Tiling

theorem right_tenth_reptiling {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hα : d.tile.angle 0 = Real.pi / 10)
    (hscalene : Function.Injective T.angle) : ReptilingAngles d.tile T := by
  have hβ : d.tile.angle 1 = 4 * (Real.pi / 10) := by linarith [d.tile.angle_sum]
  obtain ⟨c, hrow, hp, hs⟩ := d.integer_corner_weights 10 (by norm_num) ![1, 4, 5] (by
    intro j
    fin_cases j <;> norm_num
    · change d.tile.angle 0 = Real.pi / 10
      exact hα
    · change d.tile.angle 1 = (4 : ℝ) * (Real.pi / 10)
      exact hβ
    · change d.tile.angle 2 = (5 : ℝ) * (Real.pi / 10)
      linarith [hright])
  norm_num only [Nat.cast_ofNat] at hrow
  obtain ⟨e, h01, h12⟩ := ordered_integer_weights T c _ hrow hscalene
  have heSum : c (e 0) + c (e 1) + c (e 2) = 10 := (sorted_weights_sum c e).trans hs
  let d' := d.reindexOuter e.symm
  have hU (i : Fin 3) : Triangle.angle (T.reindex e.symm) i =
      (c (e i) : ℝ) * (Real.pi / 10) := by
    simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hrow (e i)
  rcases sorted_partition_ten _ _ _ (hp (e 0)) h01 h12 heSum with
    ⟨hc0, hc1, hc2⟩ | ⟨hc0, hc1, hc2⟩ | ⟨hc0, hc1, hc2⟩ | ⟨hc0, hc1, hc2⟩
  · exfalso
    apply d'.right_tenth_double_seventh_impossible hright hα
    · simpa only [hc0, Nat.cast_one, one_mul] using hU 0
    · simpa only [hc1, Nat.cast_ofNat] using hU 1
    · simpa only [hc2, Nat.cast_ofNat] using hU 2
  · exfalso
    apply d'.right_tenth_third_sixth_impossible hright hα
    · simpa only [hc0, Nat.cast_one, one_mul] using hU 0
    · simpa only [hc1, Nat.cast_ofNat] using hU 1
    · simpa only [hc2, Nat.cast_ofNat] using hU 2
  · apply reptilingAngles_of_two_matched_angles d.tile T (e 0) (e 2) 0 2
      (fun h => (by decide : (0 : Fin 3) ≠ 2) (e.injective h)) (by decide)
    · rw [hrow, hc0, Nat.cast_one, one_mul, hα]
    · rw [hrow, hc2, hright]
      norm_num
      ring
  · exfalso
    apply d'.right_tenth_second_third_impossible hright hα
    · simpa only [hc0, Nat.cast_ofNat] using hU 0
    · simpa only [hc1, Nat.cast_ofNat] using hU 1
    · have h := hU 2
      rw [hc2] at h
      norm_num at h
      linarith

end Erdos633b.Tiling
