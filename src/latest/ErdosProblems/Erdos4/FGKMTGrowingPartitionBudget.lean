import ErdosProblems.Erdos4.FGKMTCoveringParameters
import ErdosProblems.Erdos4.FGKMTGrowingPrimeSupply

/-! Cardinality, marginal, and Chernoff budgets for the actual source partition. -/

namespace Erdos4.FGKMT

open Filter Classical

theorem growingSourcePrimes_card_le (x : ℕ) : (growingSourcePrimes x).card ≤ x := by
  have hsub : growingSourcePrimes x ⊆ Finset.Icc 1 x := by
    intro p hp
    have hh := mem_growingSourcePrimes.mp hp
    exact Finset.mem_Icc.mpr ⟨hh.1.one_le, hh.2.2⟩
  simpa using Finset.card_le_card hsub

theorem growing_marginal_le_sparsity {x : ℕ} (hx : 1 ≤ x) :
    (x : ℝ) ^ (-4 / 5 : ℝ) ≤ (x : ℝ) ^ (-1 / 5 : ℝ) := by
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) (by norm_num)

theorem source_count_square_budget {x N : ℕ} (hx : 1 ≤ x) (hN : N ≤ x) :
    (N : ℝ) * ((x : ℝ) ^ (-4 / 5 : ℝ)) ^ 2 ≤ ((x : ℝ) ^ (-1 / 5 : ℝ)) ^ 2 := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hNR : (N : ℝ) ≤ x := by exact_mod_cast hN
  calc
    _ ≤ (x : ℝ) * ((x : ℝ) ^ (-4 / 5 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hNR (sq_nonneg _)
    _ = (x : ℝ) ^ (1 : ℝ) *
        ((x : ℝ) ^ (-4 / 5 : ℝ) * (x : ℝ) ^ (-4 / 5 : ℝ)) := by
      simp only [Real.rpow_one, pow_two]
    _ = (x : ℝ) ^ (-3 / 5 : ℝ) := by
      rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
      norm_num
    _ ≤ (x : ℝ) ^ (-2 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    _ = _ := by rw [pow_two, ← Real.rpow_add hxpos]; norm_num

theorem eventually_growing_partition_budget (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℕ in atTop, ∀ N : ℕ,
      (N : ℝ) ≤ A * x * (growingIndex x : ℝ) / Real.log (x : ℝ) →
      (growingRounds x : ℝ) * N *
        Real.exp (-(growingCoverDensity x) / (6 * (x : ℝ) ^ (-4 / 5 : ℝ))) < 1 := by
  filter_upwards [eventually_growing_cover_parameters,
    eventually_const_log_power_le_rpow 2 24 (by norm_num : (0 : ℝ) < 4 / 5),
    eventually_const_log_power_le_rpow 1 A (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 2] with x hpar hpower hAL hx
  intro N hN
  let L := Real.log (x : ℝ)
  let ε := (x : ℝ) ^ (-4 / 5 : ℝ)
  let κ := growingCoverDensity x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hjpos : (0 : ℝ) < growingIndex x := by exact_mod_cast hpar.1
  have hLpos : 0 < L := hjpos.trans_le hpar.2.1
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hxpos _
  have hκlow : 1 / L ≤ κ := hpar.2.2.2.1
  have hNsmall : (N : ℝ) ≤ A * x := by
    apply hN.trans
    apply (div_le_iff₀ hLpos).mpr
    exact mul_le_mul_of_nonneg_left hpar.2.1 (mul_nonneg hA hxpos.le)
  have hAL' : A * L ≤ (x : ℝ) := by
    simpa only [pow_one, Real.rpow_one] using hAL
  have hcount : (growingRounds x : ℝ) * N ≤ (x : ℝ) ^ 2 := by
    calc
      _ ≤ L * (A * x) :=
        mul_le_mul hpar.2.2.1 hNsmall (Nat.cast_nonneg N) hLpos.le
      _ = (x : ℝ) * (A * L) := by ring
      _ ≤ (x : ℝ) * x := mul_le_mul_of_nonneg_left hAL' hxpos.le
      _ = _ := by ring
  have hproduct : (x : ℝ) ^ (4 / 5 : ℝ) * ε = 1 := by
    dsimp only [ε]
    rw [← Real.rpow_add hxpos]
    norm_num
  have hsmall : 24 * L ^ 2 * ε ≤ 1 := by
    calc
      _ ≤ (x : ℝ) ^ (4 / 5 : ℝ) * ε :=
        mul_le_mul_of_nonneg_right hpower hεpos.le
      _ = _ := hproduct
  have hfour : (4 * L) * (6 * ε) ≤ κ := by
    calc
      _ ≤ 1 / L := (le_div_iff₀ hLpos).mpr (by nlinarith only [hsmall])
      _ ≤ _ := hκlow
  have hquot : 4 * L ≤ κ / (6 * ε) := (le_div_iff₀ (by positivity)).mpr hfour
  have hexp : Real.exp (-κ / (6 * ε)) ≤ (x : ℝ) ^ (-4 : ℝ) := by
    calc
      _ = Real.exp (-(κ / (6 * ε))) := by congr 1; ring
      _ ≤ Real.exp (-(4 * L)) := Real.exp_le_exp.mpr (neg_le_neg hquot)
      _ = _ := by
        rw [Real.rpow_def_of_pos hxpos]
        congr 1
        dsimp only [L]
        ring
  change (growingRounds x : ℝ) * N * Real.exp (-κ / (6 * ε)) < 1
  calc
    _ ≤ (x : ℝ) ^ 2 * (x : ℝ) ^ (-4 : ℝ) :=
      mul_le_mul hcount hexp (Real.exp_nonneg _) (sq_nonneg _)
    _ = (x : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hxpos]
      norm_num
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx1 (by norm_num)

end Erdos4.FGKMT
