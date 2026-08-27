import ErdosProblems.Erdos4.TiltedPrimeSurvivorLaw

/-! The explicit prime-degree and capped-marginal errors vanish at the required rates. -/

namespace Erdos4.Tilted

open Filter FGKMT

theorem eventually_tilted_prime_error_budget :
    ∀ᶠ x : ℕ in atTop,
      let k := sieveDimension (growingIndex x)
      let L := Real.log (x : ℝ)
      let σ := primeDensity x
      let α := (x : ℝ) ^ (-9 / 10 : ℝ)
      1 / L ^ (80 : ℕ) ≤ 1 / 16 ∧
      224 * (1 / L ^ (80 : ℕ)) + 64 * (k : ℝ) * ((k : ℝ) * α) / σ ^ (3 * k) ≤ 1 / L ^ (40 : ℕ) ∧
      ((k : ℝ) * α) / σ ^ k ≤ (x : ℝ) ^ (-4 / 5 : ℝ) := by
  filter_upwards [eventually_primeDensity_inverse_power (by norm_num : (0 : ℝ) < 1 / 20),
    eventually_growingDimension_bounds, log_tendsto.eventually (eventually_ge_atTop 448),
    eventually_const_log_power_le_rpow 1 1 (by norm_num : (0 : ℝ) < 1 / 20),
    eventually_const_log_power_le_rpow 42 128 (by norm_num : (0 : ℝ) < 4 / 5),
    eventually_ge_atTop 1] with x hinv hdim hL hxL hdom hx
  dsimp only
  let k := sieveDimension (growingIndex x)
  let L := Real.log (x : ℝ)
  let σ := primeDensity x
  let α := (x : ℝ) ^ (-9 / 10 : ℝ)
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hL1 : 1 ≤ L := by change 448 ≤ L at hL; linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hkL : (k : ℝ) ≤ L := hdim.2.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 100 : ℝ) ≤ 1))
  have hkx : (k : ℝ) ≤ (x : ℝ) ^ (1 / 20 : ℝ) := hkL.trans (by simpa only [one_mul, pow_one] using hxL)
  have hα0 : 0 ≤ α := Real.rpow_nonneg hxpos.le _
  have hσpos : 0 < σ := primeDensity_pos x
  have hσ1 : σ ≤ 1 := primeDensity_le_one x
  have hσinv : 1 / σ ^ k ≤ 1 / σ ^ (3 * k) :=
    one_div_le_one_div_of_le (pow_pos hσpos _) (pow_le_pow_of_le_one hσpos.le hσ1 (by omega))
  have hαinv : α * (1 / σ ^ (3 * k)) ≤ (x : ℝ) ^ (-4 / 5 : ℝ) := by
    calc
      _ ≤ α * (x : ℝ) ^ (1 / 20 : ℝ) := mul_le_mul_of_nonneg_left hinv hα0
      _ = (x : ℝ) ^ (-17 / 20 : ℝ) := by dsimp [α]; rw [← Real.rpow_add hxpos]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hL40 : 448 ≤ L ^ (40 : ℕ) := hL.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (40 : ℕ)))
  have hfirst : 224 * (1 / L ^ (80 : ℕ)) ≤ 1 / (2 * L ^ (40 : ℕ)) := by
    calc
      _ = (224 / L ^ (40 : ℕ)) * (1 / L ^ (40 : ℕ)) := by field_simp
      _ ≤ (1 / 2) * (1 / L ^ (40 : ℕ)) := mul_le_mul_of_nonneg_right
        ((div_le_iff₀ (pow_pos hLpos 40)).mpr (by linarith)) (by positivity)
      _ = _ := by ring
  have hsmall : (x : ℝ) ^ (-4 / 5 : ℝ) ≤ 1 / (128 * L ^ (42 : ℕ)) := by
    rw [show (-4 / 5 : ℝ) = -(4 / 5 : ℝ) by ring, Real.rpow_neg hxpos.le]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 128 * L ^ (42 : ℕ)) hdom
  have hsecond : 64 * (k : ℝ) * ((k : ℝ) * α) / σ ^ (3 * k) ≤ 1 / (2 * L ^ (40 : ℕ)) := by
    calc
      _ = 64 * (k : ℝ) ^ 2 * (α * (1 / σ ^ (3 * k))) := by ring
      _ ≤ 64 * L ^ 2 * (x : ℝ) ^ (-4 / 5 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hkL 2) (by norm_num))
          hαinv (by positivity) (by positivity)
      _ ≤ 64 * L ^ 2 * (1 / (128 * L ^ (42 : ℕ))) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by field_simp; norm_num
  refine ⟨?_, ?_, ?_⟩
  · apply (div_le_iff₀ (pow_pos hLpos 80)).mpr
    have hh : L ≤ L ^ (80 : ℕ) := by
      simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (80 : ℕ))
    change 448 ≤ L at hL
    nlinarith
  · exact (add_le_add hfirst hsecond).trans_eq (by ring)
  · calc
      _ = (k : ℝ) * α * (1 / σ ^ k) := by ring
      _ ≤ (x : ℝ) ^ (1 / 20 : ℝ) * α * (x : ℝ) ^ (1 / 20 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hkx hα0) (hσinv.trans hinv) (by positivity) (by positivity)
      _ = _ := by
        dsimp [α]
        rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
        norm_num

end Erdos4.Tilted
