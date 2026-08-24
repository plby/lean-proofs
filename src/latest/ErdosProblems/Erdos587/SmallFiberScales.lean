import ErdosProblems.Erdos587.CriticalScale

/-! Power margins for the small-coefficient unit-step fiber. -/

open Filter

namespace Erdos587

theorem eventually_small_coefficient_length :
    ∀ᶠ T : ℝ in atTop, ∀ (u J : ℝ), 0 ≤ u →
      u ≤ T ^ (1 / 16 : ℝ) → T ^ (1 / 4 : ℝ) ≤ J → 16 * u ≤ J := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 16)).eventually_ge_atTop 16]
    with T hT1 hmargin
  intro u J hu huhi hJ
  have hT : 0 < T := by linarith
  calc
    16 * u ≤ T ^ (3 / 16 : ℝ) * T ^ (1 / 16 : ℝ) := by gcongr
    _ = T ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hT]; norm_num
    _ ≤ J := hJ

theorem eventually_small_fiber_ratio {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop, ∀ (u J M : ℝ), 0 < u →
      J ≤ T ^ (1 / 4 + 1 / 1000 : ℝ) → M ≤ J / u →
      M ≤ Real.sqrt T / (D * u) := by
  have hevent := eventually_rpow_le_const_mul_rpow
    (by norm_num : (1 / 4 + 1 / 1000 : ℝ) < 1 / 2) (one_div_pos.mpr hD)
  filter_upwards [hevent] with T hscale
  intro u J M hu hJ hM
  have hJbound : J ≤ Real.sqrt T / D := by
    apply hJ.trans
    simpa only [← Real.sqrt_eq_rpow, one_div_mul_eq_div] using hscale
  calc
    M ≤ J / u := hM
    _ ≤ (Real.sqrt T / D) / u := div_le_div_of_nonneg_right hJbound hu.le
    _ = Real.sqrt T / (D * u) := by ring

theorem eventually_small_fiber_power_budget {K : ℝ} (hK : 0 < K) :
    ∀ᶠ T : ℝ in atTop, ∀ (u H J M : ℝ),
      0 < u → 0 ≤ H → 0 < J → 0 ≤ M →
      u ≤ T ^ (1 / 16 : ℝ) → J ≤ T ^ (1 / 4 + 1 / 1000 : ℝ) →
      T ^ (3 / 4 : ℝ) ≤ H * J → J ≤ 2 * u * M →
      K * T ^ 4 < u * H ^ 7 * M ^ 3 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 121 / 1000)).eventually_ge_atTop (8 * K + 1)]
    with T hT1 hlarge
  intro u H J M hu hH hJ hM huhi hJhi hprod hJM
  have hT : 0 < T := by linarith
  have hmargin : 8 * K < T ^ (121 / 1000 : ℝ) := by linarith
  have hu2 : u ^ 2 ≤ T ^ (1 / 8 : ℝ) := by
    have hh := pow_le_pow_left₀ hu.le huhi 2
    rw [← Real.rpow_mul_natCast hT.le] at hh
    norm_num at hh
    exact hh
  have hJ4 : J ^ 4 ≤ T ^ (251 / 250 : ℝ) := by
    have hh := pow_le_pow_left₀ hJ.le hJhi 4
    rw [← Real.rpow_mul_natCast hT.le] at hh
    norm_num at hh
    exact hh
  have hprod7 : T ^ (21 / 4 : ℝ) ≤ H ^ 7 * J ^ 7 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hT.le _) hprod 7
    rw [← Real.rpow_mul_natCast hT.le, mul_pow] at hh
    norm_num at hh
    exact hh
  have hJ3 : J ^ 3 ≤ 8 * u ^ 3 * M ^ 3 := by
    have hh := pow_le_pow_left₀ hJ.le hJM 3
    simpa only [mul_pow, show (2 : ℝ) ^ 3 = 8 by norm_num] using hh
  have hscale : T ^ 4 * T ^ (1 / 8 : ℝ) * T ^ (251 / 250 : ℝ) = T ^ (5129 / 1000 : ℝ) := by
    rw [← Real.rpow_natCast T 4, ← Real.rpow_add hT, ← Real.rpow_add hT]
    norm_num
  have hscalemargin : T ^ (121 / 1000 : ℝ) * T ^ (5129 / 1000 : ℝ) = T ^ (21 / 4 : ℝ) := by
    rw [← Real.rpow_add hT]
    norm_num
  have hstrict : K * T ^ 4 * (8 * u ^ 2 * J ^ 4) < T ^ (21 / 4 : ℝ) := by
    calc
      _ = (8 * K) * (T ^ 4 * u ^ 2 * J ^ 4) := by ring
      _ ≤ (8 * K) * (T ^ 4 * T ^ (1 / 8 : ℝ) * T ^ (251 / 250 : ℝ)) := by gcongr
      _ = (8 * K) * T ^ (5129 / 1000 : ℝ) := by rw [hscale]
      _ < T ^ (121 / 1000 : ℝ) * T ^ (5129 / 1000 : ℝ) :=
        mul_lt_mul_of_pos_right hmargin (Real.rpow_pos_of_pos hT _)
      _ = _ := hscalemargin
  have hupper : H ^ 7 * J ^ 7 ≤ (u * H ^ 7 * M ^ 3) * (8 * u ^ 2 * J ^ 4) := by
    calc
      _ = H ^ 7 * J ^ 3 * J ^ 4 := by ring
      _ ≤ H ^ 7 * (8 * u ^ 3 * M ^ 3) * J ^ 4 := by gcongr
      _ = _ := by ring
  exact (mul_lt_mul_iff_left₀ (by positivity : 0 < 8 * u ^ 2 * J ^ 4)).mp
    (hstrict.trans_le (hprod7.trans hupper))

end Erdos587
