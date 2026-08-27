import ErdosProblems.Erdos4.FGKMTGrowingPartitionBudget

/-! The prime source partition is valid for every possible survivor set, up to `x²` vertices. -/

namespace Erdos4.Tilted

open FGKMT Filter

theorem eventually_prime_partition_budget :
    ∀ᶠ x : ℕ in atTop, ∀ N : ℕ, N ≤ x ^ 2 →
      (growingRounds x : ℝ) * N *
        Real.exp (-(growingCoverDensity x) / (6 * (x : ℝ) ^ (-4 / 5 : ℝ))) < 1 := by
  filter_upwards [eventually_growing_cover_parameters,
    eventually_const_log_power_le_rpow 2 24 (by norm_num : (0 : ℝ) < 4 / 5),
    eventually_ge_atTop 2] with x hpar hpower hx
  intro N hN
  let L := Real.log (x : ℝ)
  let ε := (x : ℝ) ^ (-4 / 5 : ℝ)
  let κ := growingCoverDensity x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hjpos : (0 : ℝ) < growingIndex x := by exact_mod_cast hpar.1
  have hLpos : 0 < L := hjpos.trans_le hpar.2.1
  have hLx : L ≤ x := by have hh := Real.log_le_sub_one_of_pos hxpos; change L ≤ _ at hh; linarith
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hxpos _
  have hκlow : 1 / L ≤ κ := hpar.2.2.2.1
  have hcount : (growingRounds x : ℝ) * N ≤ (x : ℝ) ^ 3 := by
    calc
      _ ≤ (x : ℝ) * (x : ℝ) ^ 2 :=
        mul_le_mul (hpar.2.2.1.trans hLx) (by exact_mod_cast hN) (Nat.cast_nonneg _) hxpos.le
      _ = _ := by ring
  have hproduct : (x : ℝ) ^ (4 / 5 : ℝ) * ε = 1 := by
    dsimp only [ε]
    rw [← Real.rpow_add hxpos]
    norm_num
  have hsmall : 24 * L ^ 2 * ε ≤ 1 :=
    (mul_le_mul_of_nonneg_right hpower hεpos.le).trans_eq hproduct
  have hfour : (4 * L) * (6 * ε) ≤ κ := by
    calc
      _ ≤ 1 / L := (le_div_iff₀ hLpos).mpr (by nlinarith only [hsmall])
      _ ≤ _ := hκlow
  have hquot : 4 * L ≤ κ / (6 * ε) := (le_div_iff₀ (by positivity)).mpr hfour
  have hexp : Real.exp (-κ / (6 * ε)) ≤ (x : ℝ) ^ (-4 : ℝ) := by
    calc
      _ = Real.exp (-(κ / (6 * ε))) := by congr 1; ring
      _ ≤ Real.exp (-(4 * L)) := Real.exp_le_exp.mpr (neg_le_neg hquot)
      _ = _ := by rw [Real.rpow_def_of_pos hxpos]; congr 1; dsimp only [L]; ring
  change (growingRounds x : ℝ) * N * Real.exp (-κ / (6 * ε)) < 1
  calc
    _ ≤ (x : ℝ) ^ 3 * (x : ℝ) ^ (-4 : ℝ) :=
      mul_le_mul hcount hexp (Real.exp_nonneg _) (by positivity)
    _ = (x : ℝ) ^ (-1 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_add hxpos]; norm_num
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx1 (by norm_num)

end Erdos4.Tilted
