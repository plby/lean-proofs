import StackExchange.Puzzling139335.GlideCrossing.SecondLarge
import StackExchange.Puzzling139335.GlideCrossing.SmallCubic

namespace Puzzling139335.GlideCrossing

private theorem secondBound_halfAngle {c s t : ℝ} (hc : 0 ≤ c)
    (hcircle : c ^ 2 + s ^ 2 = 1) (ht : t = s / (1 + c)) :
    s = 2 * t / (1 + t ^ 2) ∧ c = (1 - t ^ 2) / (1 + t ^ 2) := by
  have hden : 1 + c ≠ 0 := by positivity
  have htden : 1 + (s / (1 + c)) ^ 2 = 2 / (1 + c) := by
    field_simp
    nlinarith [hcircle]
  subst t
  constructor
  · rw [htden]
    field_simp
  · rw [htden]
    field_simp
    nlinarith [hcircle]

/-- The full second strict lower bound, including both sum-angle branches. -/
theorem secondLowerBound_pos (α β : ℝ)
    (hαlo : Real.pi / 3 ≤ α) (hβpos : 0 < β) (hβα : β ≤ α)
    (hαhi : α < Real.pi / 2) (hprod : 4 * Real.cos α * Real.cos β ≤ 1) :
    0 < Real.sin β - (1 + Real.cos (α - β)) / 2 + Real.cos β *
      (1 / 2 + Real.cos α - (1 + 2 * Real.cos α) *
        min (Real.sin β / (1 + Real.cos β)) (Real.cos α / (1 + Real.sin α))) := by
  have hπ := Real.pi_pos
  have hα0 : 0 < α := by linarith
  have hαπ : α ≤ Real.pi := by linarith
  have hβπ : β ≤ Real.pi := by linarith
  have hC : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hαhi⟩
  have hCh : Real.cos α ≤ 1 / 2 := by
    simpa only [Real.cos_pi_div_three] using
      (Real.cos_le_cos_of_nonneg_of_le_pi
        (show 0 ≤ Real.pi / 3 by positivity) hαπ hαlo)
  have hS : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα0.le hαπ
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβpos (by linarith)
  have hdenS : 0 < 1 + Real.sin α := by positivity
  have hdenc : 0 < 1 + Real.cos β := by positivity
  have hcircle := Real.cos_sq_add_sin_sq α
  have hS1 : Real.sin α < 1 := by nlinarith [sq_pos_of_pos hC]
  by_cases hsum : Real.pi / 2 ≤ α + β
  · have hsc : Real.cos α ≤ Real.sin β := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two
        (show -(Real.pi / 2) ≤ Real.pi / 2 - α by linarith)
        (show β ≤ Real.pi / 2 by linarith)
        (show Real.pi / 2 - α ≤ β by linarith)
      simpa only [Real.sin_pi_div_two_sub] using h
    have hcS : Real.cos β ≤ Real.sin α := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi
        (show 0 ≤ Real.pi / 2 - α by linarith) hβπ
        (show Real.pi / 2 - α ≤ β by linarith)
      simpa only [Real.cos_pi_div_two_sub] using h
    have horder : Real.cos α / (1 + Real.sin α) ≤
        Real.sin β / (1 + Real.cos β) := by
      apply (div_le_div_iff₀ hdenS hdenc).2
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hcS),
        mul_nonneg (sub_nonneg.mpr hsc) hdenS.le]
    rw [min_eq_right horder]
    have hid : Real.sin β - (1 + Real.cos (α - β)) / 2 + Real.cos β *
        (1 / 2 + Real.cos α - (1 + 2 * Real.cos α) *
          (Real.cos α / (1 + Real.sin α))) =
        (1 - Real.sin α / 2) * Real.sin β +
          (1 / 2 + Real.cos α * (Real.sin α - 1 - 4 * Real.cos α) /
            (2 * (1 + Real.sin α))) * Real.cos β - 1 / 2 := by
      rw [Real.cos_sub]
      field_simp
      ring
    rw [hid]
    exact secondLarge_pos α β hαlo hβpos hβα hαhi hprod hsum
  · have hsum' : α + β ≤ Real.pi / 2 := le_of_lt (lt_of_not_ge hsum)
    have hsC : Real.sin β ≤ Real.cos α := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two
        (show -(Real.pi / 2) ≤ β by linarith)
        (show Real.pi / 2 - α ≤ Real.pi / 2 by linarith)
        (show β ≤ Real.pi / 2 - α by linarith)
      simpa only [Real.sin_pi_div_two_sub] using h
    have hSc : Real.sin α ≤ Real.cos β := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi hβpos.le
        (show Real.pi / 2 - α ≤ Real.pi by linarith)
        (show β ≤ Real.pi / 2 - α by linarith)
      simpa only [Real.cos_pi_div_two_sub] using h
    have horder : Real.sin β / (1 + Real.cos β) ≤
        Real.cos α / (1 + Real.sin α) := by
      apply (div_le_div_iff₀ hdenc hdenS).2
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hSc),
        mul_nonneg (sub_nonneg.mpr hsC) hdenS.le]
    have hS56 : 5 / 6 < Real.sin α := by nlinarith
    have hCS : 4 * Real.cos α * Real.sin α ≤ 1 := by
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hSc)]
    have hC03 : Real.cos α < 3 / 10 := by
      nlinarith [mul_pos hC (sub_pos.mpr hS56)]
    have hS09 : 9 / 10 < Real.sin α := by nlinarith
    let t : ℝ := Real.sin β / (1 + Real.cos β)
    have ht0 : 0 ≤ t := (div_pos hs hdenc).le
    have ht1 : t ≤ Real.cos α / (1 + Real.sin α) := horder
    have hP := smallCubic_pos hC hC03 hS09 hS1 hcircle ht0 ht1
    obtain ⟨hsparam, hcparam⟩ :=
      secondBound_halfAngle hc.le (Real.cos_sq_add_sin_sq β) (rfl : t = _)
    rw [min_eq_left horder]
    change 0 < Real.sin β - (1 + Real.cos (α - β)) / 2 + Real.cos β *
      (1 / 2 + Real.cos α - (1 + 2 * Real.cos α) * t)
    have hid : 2 * (1 + t ^ 2) *
        (Real.sin β - (1 + Real.cos (α - β)) / 2 + Real.cos β *
          (1 / 2 + Real.cos α - (1 + 2 * Real.cos α) * t)) =
        smallCubic (Real.cos α) (Real.sin α) t := by
      rw [Real.cos_sub, hsparam, hcparam]
      convert smallCubic_halfAngle_identity (Real.cos α) (Real.sin α) t using 1
      ring
    have hmult : 0 < 2 * (1 + t ^ 2) *
        (Real.sin β - (1 + Real.cos (α - β)) / 2 + Real.cos β *
          (1 / 2 + Real.cos α - (1 + 2 * Real.cos α) * t)) := by
      rw [hid]
      exact hP
    exact pos_of_mul_pos_right hmult (by positivity)

end Puzzling139335.GlideCrossing
