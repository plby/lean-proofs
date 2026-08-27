import ErdosProblems.Erdos4.FGKMTInitialErrorBudget
import ErdosProblems.Erdos4.FGKMTGrowingRadius

/-! The chosen interval has the full FGKMT18 length and satisfies all finite window requirements. -/

namespace Erdos4.FGKMT

open Filter

theorem eventually_growing_gap_length_bounds {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      1 ≤ growingGapLength c x ∧ x ≤ growingGapLength c x ∧
      growingPrecutoff x * x ≤ growingGapLength c x ∧
      growingGapLength c x ≤ x ^ 2 ∧ 3 * growingGapLength c x ≤ x ^ 3 ∧
      (c / 2) * (x : ℝ) * growingOuterScale x ≤ (growingGapLength c x : ℝ) ∧
      (growingGapLength c x : ℝ) ≤ c * (x : ℝ) * growingOuterScale x := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hquarter := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hlog
  filter_upwards [eventually_growing_outer_log_budget, eventually_growingPrecutoff_bounds,
    hquarter.eventually (eventually_ge_atTop (2 / c)),
    eventually_const_log_power_le_rpow 1 c (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 3] with x hb hD hlarge hcl hx
  let L := Real.log (x : ℝ)
  let t := L ^ (1 / 4 : ℝ)
  let s := growingOuterScale x
  let raw := c * (x : ℝ) * s
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hb.1
  have ht0 : 0 ≤ t := Real.rpow_nonneg hLpos.le _
  have ht2 : t ^ (2 : ℕ) = Real.sqrt L := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
    exact (Real.sqrt_eq_rpow L).symm
  have hsroot : Real.sqrt L ≤ s := by
    have hh := hb.2.2.2.1
    change Real.sqrt L ≤ s / 100 at hh
    nlinarith [Real.sqrt_nonneg L]
  have hs : 0 < s := (Real.sqrt_pos.mpr hLpos).trans_le hsroot
  have hct : 2 ≤ c * t := by
    change 2 / c ≤ t at hlarge
    have hh := (div_le_iff₀ hc).mp hlarge
    nlinarith
  have hcs : 2 * (growingPrecutoff x : ℝ) ≤ c * s := by
    calc
      _ ≤ 2 * t := mul_le_mul_of_nonneg_left hD.2.2 (by norm_num)
      _ ≤ c * t ^ (2 : ℕ) := by nlinarith [mul_le_mul_of_nonneg_right hct ht0]
      _ ≤ c * s := mul_le_mul_of_nonneg_left (ht2 ▸ hsroot) hc.le
  have hrawlower : 2 * (growingPrecutoff x : ℝ) * x ≤ raw := by
    have hh := mul_le_mul_of_nonneg_right hcs hxpos.le
    dsimp only [raw]
    nlinarith
  have hD2 : (2 : ℝ) ≤ growingPrecutoff x := by exact_mod_cast hD.1
  have hraw2 : 2 ≤ raw := by nlinarith
  have hhalf : raw / 2 ≤ (growingGapLength c x : ℝ) := by
    have hh := Nat.lt_floor_add_one raw
    change raw < (growingGapLength c x : ℝ) + 1 at hh
    linarith
  have hmain : growingPrecutoff x * x ≤ growingGapLength c x := by
    have hh : (growingPrecutoff x : ℝ) * x ≤ (growingGapLength c x : ℝ) := by linarith
    exact_mod_cast hh
  have hXY : x ≤ growingGapLength c x := by
    calc
      _ ≤ growingPrecutoff x * x := by nlinarith [hD.1]
      _ ≤ _ := hmain
  have hupper : (growingGapLength c x : ℝ) ≤ raw := Nat.floor_le (by positivity)
  have hYx : growingGapLength c x ≤ x ^ 2 := by
    have hcl' : c * L ≤ (x : ℝ) := by simpa only [pow_one, Real.rpow_one] using hcl
    have hrawup : raw ≤ (x : ℝ) ^ (2 : ℕ) := by
      calc
        _ ≤ c * (x : ℝ) * L := mul_le_mul_of_nonneg_left hb.2.2.2.2 (by positivity)
        _ = (x : ℝ) * (c * L) := by ring
        _ ≤ (x : ℝ) * x := mul_le_mul_of_nonneg_left hcl' hxpos.le
        _ = _ := by ring
    exact_mod_cast hupper.trans hrawup
  have hY3 : 3 * growingGapLength c x ≤ x ^ 3 := by
    calc
      _ ≤ 3 * x ^ 2 := Nat.mul_le_mul_left 3 hYx
      _ ≤ x * x ^ 2 := Nat.mul_le_mul_right (x ^ 2) hx
      _ = _ := by ring
  refine ⟨(show 1 ≤ x by omega).trans hXY, hXY, hmain, hYx, hY3, ?_, hupper⟩
  have heq : (c / 2) * (x : ℝ) * s = raw / 2 := by dsimp only [raw]; ring
  exact heq.le.trans hhalf

theorem eventually_growing_random_end_le_radius :
    ∀ᶠ x : ℕ in atTop, growingRandomEnd x ≤ growingRadius x := by
  filter_upwards [eventually_growing_outer_log_budget, eventually_ge_atTop 1] with x hb hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  unfold growingRandomEnd growingRadius
  apply Nat.floor_le_floor
  calc
    _ ≤ Real.exp (Real.log (x : ℝ) / 100) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hb.2.2.2.2 (by norm_num))
    _ = (x : ℝ) ^ (1 / 100 : ℝ) := by
      rw [Real.rpow_def_of_pos hxpos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 100 : ℝ) ≤ 1 / 50)

end Erdos4.FGKMT
