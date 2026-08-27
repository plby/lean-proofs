import ErdosProblems.Erdos4.TiltedBlockVariance
import ErdosProblems.Erdos4.FGKMTInitialErrorBudget
import Mathlib.Data.Nat.Sqrt

/-! Elementary cutoff comparisons and a uniform logarithmic variance budget. -/

namespace Erdos4.Tilted

open FGKMT Filter

theorem floor_cutoff_ge_pow {L : ℝ} (hL : 2 ≤ L) :
    L ^ (98 : ℕ) ≤ (⌊L ^ (100 : ℕ)⌋₊ : ℝ) := by
  have hL1 : 1 ≤ L := by linarith
  have h98 : 1 ≤ L ^ (98 : ℕ) := one_le_pow₀ hL1
  have hmul : L ^ (98 : ℕ) * L ^ (2 : ℕ) = L ^ (100 : ℕ) := by rw [← pow_add]
  have hfloor := Nat.lt_floor_add_one (L ^ (100 : ℕ))
  nlinarith [mul_nonneg (show 0 ≤ L ^ 2 - 4 by nlinarith) (show 0 ≤ L ^ 98 by positivity)]

theorem rpow_quarter_le_nat_sqrt {x : ℕ} (hx : 16 ≤ x) :
    (x : ℝ) ^ (1 / 4 : ℝ) ≤ (Nat.sqrt x : ℝ) := by
  have hR : 4 ≤ Nat.sqrt x := Nat.le_sqrt.mpr hx
  have hsq : Nat.sqrt x + 1 ≤ (Nat.sqrt x) ^ 2 := by nlinarith
  have hxR : x ≤ (Nat.sqrt x) ^ 4 := by
    have hh := (Nat.lt_succ_sqrt' x).le.trans (Nat.pow_le_pow_left hsq 2)
    simpa only [Nat.succ_eq_add_one, ← pow_mul] using hh
  calc
    _ ≤ ((Nat.sqrt x : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg x) (by exact_mod_cast hxR) (by norm_num)
    _ = _ := by
      simpa using Real.pow_rpow_inv_natCast (Nat.cast_nonneg (Nat.sqrt x))
        (by decide : (4 : ℕ) ≠ 0)

theorem variance_log_budget {x L B b γ η : ℝ}
    (hx : 0 < x) (hL : 8 ≤ L) (_hB0 : 0 ≤ B) (hB : B ≤ x ^ (1 / 16 : ℝ))
    (hb0 : 0 ≤ b) (hb : b ≤ L ^ 2 / x)
    (hγ : γ ≤ 1 / L ^ 40) (hη0 : 0 ≤ η) (hη : η ≤ 1 / L ^ 40)
    (hdom : L ^ 42 ≤ x ^ (15 / 16 : ℝ)) :
    B * b + (Real.exp γ * (1 + η) - 1) ≤ 1 / L ^ 30 := by
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  let e := 1 / L ^ 40
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hL40 : 8 ≤ L ^ 40 := hL.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (40 : ℕ)))
  have hehalf : e ≤ 1 / 2 := by
    dsimp [e]
    apply (div_le_iff₀ (pow_pos hLpos 40)).mpr
    linarith
  have hexp : Real.exp γ ≤ 1 + 2 * e := by
    have hh := exp_sub_one_le_of_half_budget (show 0 ≤ 2 * e by positivity)
      (show 2 * e ≤ 1 by linarith) (show γ ≤ (2 * e) / 2 by dsimp [e]; linarith)
    linarith
  have hcorr : Real.exp γ * (1 + η) - 1 ≤ 4 * e := by
    have hm := mul_le_mul hexp (show 1 + η ≤ 1 + e by dsimp [e]; linarith)
      (show 0 ≤ 1 + η by linarith) (show 0 ≤ 1 + 2 * e by linarith)
    nlinarith [mul_nonneg he0 (show 0 ≤ 1 / 2 - e by linarith)]
  have hxsplit : x ^ (1 / 16 : ℝ) * x ^ (15 / 16 : ℝ) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  have hdiag : B * b ≤ e := by
    calc
      _ ≤ x ^ (1 / 16 : ℝ) * (L ^ 2 / x) :=
        mul_le_mul hB hb hb0 (Real.rpow_nonneg hx.le _)
      _ = L ^ 2 / x ^ (15 / 16 : ℝ) := by
        field_simp [hx.ne', (Real.rpow_pos_of_pos hx (15 / 16 : ℝ)).ne']
        nlinarith only [hxsplit]
      _ ≤ L ^ 2 / L ^ 42 := div_le_div_of_nonneg_left (sq_nonneg L) (pow_pos hLpos 42) hdom
      _ = e := by dsimp [e]; field_simp
  have h510 : 5 ≤ L ^ (10 : ℕ) := (show 5 ≤ L by linarith).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (10 : ℕ)))
  have hsmall : 5 * e ≤ 1 / L ^ 30 := by
    calc
      _ = (5 / L ^ 10) * (1 / L ^ 30) := by dsimp [e]; field_simp
      _ ≤ 1 * (1 / L ^ 30) := mul_le_mul_of_nonneg_right
        ((div_le_one (pow_pos hLpos 10)).mpr h510) (by positivity)
      _ = _ := one_mul _
  exact (show B * b + (Real.exp γ * (1 + η) - 1) ≤ 5 * e by linarith).trans hsmall

theorem eventually_variance_budget :
    ∀ᶠ x : ℕ in atTop, ∀ B b γ η : ℝ,
      0 ≤ B → B ≤ (x : ℝ) ^ (1 / 16 : ℝ) →
      0 ≤ b → b ≤ Real.log (x : ℝ) ^ (2 : ℕ) / x →
      γ ≤ 1 / Real.log (x : ℝ) ^ (40 : ℕ) →
      0 ≤ η → η ≤ 1 / Real.log (x : ℝ) ^ (40 : ℕ) →
      B * b + (Real.exp γ * (1 + η) - 1) ≤ 1 / Real.log (x : ℝ) ^ (30 : ℕ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlog.eventually (eventually_ge_atTop 8), eventually_ge_atTop 1,
    eventually_const_log_power_le_rpow 42 1 (by norm_num : (0 : ℝ) < 15 / 16)]
    with x hL hx hdom
  intro B b γ η hB0 hB hb0 hb hγ hη0 hη
  apply variance_log_budget (x := (x : ℝ)) (L := Real.log (x : ℝ))
    (by exact_mod_cast hx) hL hB0 hB hb0 hb hγ hη0 hη
  simpa only [one_mul] using hdom

end Erdos4.Tilted
