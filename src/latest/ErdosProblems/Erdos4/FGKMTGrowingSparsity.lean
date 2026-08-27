import ErdosProblems.Erdos4.FGKMTCoveringParameters
import ErdosProblems.Erdos4.FGKMTThresholdLowerBound
import ErdosProblems.Erdos4.FGKMTSourceCovering

/-! The concrete growing dimension satisfies the full iterated covering sparsity budget. -/

namespace Erdos4.FGKMT

open Filter

theorem eventually_growing_fifth_power_budget :
    ∀ᶠ x : ℕ in atTop,
      256 * (sieveDimension (growingIndex x) : ℝ) ^ 5 ≤ Real.log (x : ℝ) / 5 := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hgrow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 19 / 20)).comp hlog
  filter_upwards [eventually_growingDimension_bounds,
    hgrow.eventually (eventually_ge_atTop 1280), hlog.eventually (eventually_ge_atTop 1)]
    with x hdim hlarge hL
  let L := Real.log (x : ℝ)
  change 1 ≤ L at hL
  change 1280 ≤ L ^ (19 / 20 : ℝ) at hlarge
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hk5 : (sieveDimension (growingIndex x) : ℝ) ^ 5 ≤ L ^ (1 / 20 : ℝ) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hdim.2 5).trans_eq
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have hh : 1280 * L ^ (1 / 20 : ℝ) ≤ L := by
    calc
      _ ≤ L ^ (19 / 20 : ℝ) * L ^ (1 / 20 : ℝ) :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hLpos.le _)
      _ = L := by rw [← Real.rpow_add hLpos]; norm_num
  have hm := mul_le_mul_of_nonneg_left hk5 (by norm_num : (0 : ℝ) ≤ 1280)
  change 256 * (sieveDimension (growingIndex x) : ℝ) ^ 5 ≤ L / 5
  linarith

theorem eventually_growing_cover_sparsity :
    ∀ᶠ x : ℕ in atTop,
      let k := sieveDimension (growingIndex x)
      (x : ℝ) ^ (-1 / 5 : ℝ) ≤
        coveringThreshold k (2 * k) (growingCoverDensity x)
          (-Real.log (1 / 2 : ℝ)) ^ (4 * 8 ^ growingRounds x) := by
  filter_upwards [eventually_growing_cover_parameters,
    eventually_growing_fifth_power_budget, eventually_ge_atTop 1] with x hpar hbudget hx
  let k := sieveDimension (growingIndex x)
  let m := growingRounds x
  let κ := growingCoverDensity x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hk : 1 ≤ k := by unfold k sieveDimension; exact Nat.one_le_two_pow
  have hκ : 0 < κ := by unfold κ growingCoverDensity; positivity
  have hκlow : 1 / (k : ℝ) ≤ κ := hpar.2.2.2.2.1
  have hD : 0 ≤ -Real.log (1 / 2 : ℝ) :=
    neg_nonneg.mpr (Real.log_nonpos (by norm_num) (by norm_num))
  have hthreshold := coveringThreshold_exp_lower hk hκ hκlow hD neg_log_half_le_one
  have hpower : (8 ^ m : ℝ) ≤ (k : ℝ) ^ 3 := by
    exact_mod_cast growingRounds_power_bound hpar.1
  have hcoef : ((4 * 8 ^ m : ℕ) : ℝ) * (64 * (k : ℝ) ^ 2) ≤
      256 * (k : ℝ) ^ 5 := by
    have hh := mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 256 * (k : ℝ) ^ 2)
    push_cast
    nlinarith only [hh]
  have hfinal : ((4 * 8 ^ m : ℕ) : ℝ) * (64 * (k : ℝ) ^ 2) ≤
      Real.log (x : ℝ) / 5 := hcoef.trans hbudget
  change (x : ℝ) ^ (-1 / 5 : ℝ) ≤
    coveringThreshold k (2 * k) κ (-Real.log (1 / 2 : ℝ)) ^ (4 * 8 ^ m)
  calc
    _ = Real.exp (-(Real.log (x : ℝ) / 5)) := by
      rw [Real.rpow_def_of_pos hxpos]
      congr 1
      ring
    _ ≤ Real.exp (-(((4 * 8 ^ m : ℕ) : ℝ) * (64 * (k : ℝ) ^ 2))) :=
      Real.exp_le_exp.mpr (neg_le_neg hfinal)
    _ = Real.exp (-(64 * (k : ℝ) ^ 2)) ^ (4 * 8 ^ m) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hthreshold _

end Erdos4.FGKMT
