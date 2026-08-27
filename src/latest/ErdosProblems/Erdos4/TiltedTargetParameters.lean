import ErdosProblems.Erdos4.TiltedParameters

/-! The actual interval has the claimed order and satisfies the prime-exposure window conditions. -/

namespace Erdos4.Tilted

open Filter FGKMT

theorem eventually_gapTarget_bounds {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      1 ≤ gapTarget c x ∧ x ≤ gapTarget c x ∧
      growingPrecutoff x * x ≤ gapTarget c x ∧
      gapTarget c x ≤ x ^ 2 ∧ 3 * gapTarget c x ≤ x ^ 3 ∧
      (c / 2) * (x : ℝ) * outerScale x ≤ (gapTarget c x : ℝ) ∧
      (gapTarget c x : ℝ) ≤ c * (x : ℝ) * outerScale x ∧
      (gapTarget c x : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) ∧
      (c / 4) * (x : ℝ) * outerScale x ≤ ((gapTarget c x - x : ℕ) : ℝ) := by
  have hquarter := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp log_tendsto
  filter_upwards [eventually_outerScale_bounds, eventually_growingPrecutoff_bounds,
    hquarter.eventually (eventually_ge_atTop (2 / c)),
    tiltScale_tendsto.eventually (eventually_ge_atTop c), eventually_ge_atTop 3]
    with x hb hD hquarter ht hx
  let L := Real.log (x : ℝ)
  let q := L ^ (1 / 4 : ℝ)
  let s := outerScale x
  let raw := c * (x : ℝ) * s
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hLpos : 0 < L := by have hh := hb.1; change 16 ≤ L at hh; linarith
  have htpos : 0 < tiltScale x := by linarith [hb.2.2.1]
  have hspos : 0 < s := div_pos hLpos htpos
  have hq0 : 0 ≤ q := Real.rpow_nonneg hLpos.le _
  have hq2 : q ^ (2 : ℕ) = Real.sqrt L := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
    exact (Real.sqrt_eq_rpow L).symm
  have hcq : 2 ≤ c * q := by
    change 2 / c ≤ q at hquarter
    have hh := (div_le_iff₀ hc).mp hquarter
    nlinarith
  have hDq : (growingPrecutoff x : ℝ) ≤ q := hD.2.2
  have hcs : 2 * (growingPrecutoff x : ℝ) ≤ c * s := by
    calc
      _ ≤ 2 * q := mul_le_mul_of_nonneg_left hDq (by norm_num)
      _ ≤ c * q ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hcq hq0]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hq2 ▸ hb.2.2.2.2.1) hc.le
  have hrawLower : 2 * (growingPrecutoff x : ℝ) * x ≤ raw := by
    have hh := mul_le_mul_of_nonneg_right hcs hxpos.le
    dsimp [raw]
    nlinarith
  have hD2 : (2 : ℝ) ≤ growingPrecutoff x := by exact_mod_cast hD.1
  have hraw2 : 2 ≤ raw := by nlinarith
  have hhalf : raw / 2 ≤ (gapTarget c x : ℝ) := by
    have hh := Nat.lt_floor_add_one raw
    change raw < (gapTarget c x : ℝ) + 1 at hh
    linarith
  have hDY : growingPrecutoff x * x ≤ gapTarget c x := by
    have hh : (growingPrecutoff x : ℝ) * x ≤ (gapTarget c x : ℝ) := by linarith
    exact_mod_cast hh
  have h2x : 2 * x ≤ gapTarget c x := (Nat.mul_le_mul_right x hD.1).trans hDY
  have hXY : x ≤ gapTarget c x := by omega
  have hupper : (gapTarget c x : ℝ) ≤ raw := Nat.floor_le (by positivity)
  have hcscale : c * s ≤ L := by
    change c * (L / tiltScale x) ≤ L
    rw [← mul_div_assoc]
    apply (div_le_iff₀ htpos).mpr
    nlinarith
  have hYL : (gapTarget c x : ℝ) ≤ (x : ℝ) * L := by
    apply hupper.trans
    have hh := mul_le_mul_of_nonneg_left hcscale hxpos.le
    dsimp [raw]
    nlinarith
  have hY2 : gapTarget c x ≤ x ^ 2 := by
    have hLx : L ≤ (x : ℝ) := by linarith [Real.log_le_sub_one_of_pos hxpos]
    have hh := hYL.trans (mul_le_mul_of_nonneg_left hLx hxpos.le)
    rw [pow_two]
    exact_mod_cast hh
  have h3Y : 3 * gapTarget c x ≤ x ^ 3 := by nlinarith
  have hlength : (c / 4) * (x : ℝ) * s ≤ ((gapTarget c x - x : ℕ) : ℝ) := by
    rw [Nat.cast_sub hXY]
    have hh : (2 : ℝ) * x ≤ (gapTarget c x : ℝ) := by exact_mod_cast h2x
    dsimp [raw] at hhalf
    nlinarith
  refine ⟨by omega, hXY, hDY, hY2, h3Y, ?_, hupper, hYL, hlength⟩
  dsimp [raw] at hhalf
  linarith

end Erdos4.Tilted
