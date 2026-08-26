import ErdosProblems.Erdos380.ParameterGrowth
import ErdosProblems.Erdos380.ShortExcessReduction

/-! # Verification of the parameters in the short-interval estimate -/

open Filter
open scoped Topology

namespace Erdos380

lemma scaleBase_le_pow (N a : ℕ) (ha : a ≠ 0) : scaleBase N ≤ scaleBase N ^ a :=
  le_self_pow (one_le_scaleBase N) ha

theorem eventually_shortWidth_le_mixingBase :
    ∀ᶠ N : ℕ in atTop, shortWidth N ≤ mixingBase N := by
  filter_upwards [eventually_logarithmicCeiling_pow_le_scaleBase 20] with N hN
  exact hN.trans (scaleBase_le_pow N 10 (by decide))

theorem eventually_shortWidth_mixing_bound (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      (shortWidth N : ℝ) * (C * (Real.log (mixingBase N : ℝ) ^ 5 / mixingBase N)) ≤ 1 := by
  have hScast : Tendsto (fun N => (scaleBase N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp scaleBase_tendsto_atTop
  filter_upwards [eventually_logarithmicCeiling_pow_le_scaleBase 20,
    eventually_log_pow_le_scaleBase 5, eventually_scaleBase_pow_le 1,
    hScast.eventually (eventually_ge_atTop (C * 100000)),
    log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with N hW hLpow hSN hCS hL
  have hS1 : (1 : ℝ) ≤ scaleBase N := by exact_mod_cast one_le_scaleBase N
  have hS : (0 : ℝ) < scaleBase N := by linarith
  have hW' : (shortWidth N : ℝ) ≤ scaleBase N := by exact_mod_cast hW
  have hsL : Real.log (scaleBase N : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log hS
    exact_mod_cast (by simpa only [pow_one] using hSN)
  have hs0 : 0 ≤ Real.log (scaleBase N : ℝ) := Real.log_nonneg hS1
  have hnum : (shortWidth N : ℝ) * C * Real.log (mixingBase N : ℝ) ^ 5 ≤ mixingBase N := by
    rw [mixingBase, Nat.cast_pow, Real.log_pow]
    push_cast
    calc
      (shortWidth N : ℝ) * C * (10 * Real.log (scaleBase N : ℝ)) ^ 5 ≤
          (scaleBase N : ℝ) * C * (10 * Real.log N) ^ 5 := by gcongr
      _ = (scaleBase N : ℝ) * (C * 100000) * Real.log N ^ 5 := by ring
      _ ≤ (scaleBase N : ℝ) * scaleBase N * scaleBase N := by gcongr
      _ = (scaleBase N : ℝ) ^ 3 := by ring
      _ ≤ (scaleBase N : ℝ) ^ 10 := pow_le_pow_right₀ hS1 (by decide)
  have hT : (0 : ℝ) < mixingBase N := by
    dsimp [mixingBase]
    exact_mod_cast pow_pos (show 0 < scaleBase N by exact_mod_cast hS) 10
  have hquot := (div_le_one hT).mpr hnum
  simpa only [mul_div_assoc, mul_assoc] using hquot

lemma log_nat_sqrt_lower {N : ℕ} (hN : 1 ≤ N)
    (hL : 3 * Real.log 4 ≤ Real.log (N : ℝ)) :
    Real.log (N : ℝ) / 3 ≤ Real.log (Nat.sqrt N : ℝ) := by
  have hm : 1 ≤ Nat.sqrt N := by simpa using Nat.sqrt_le_sqrt hN
  have hmR : (1 : ℝ) ≤ Nat.sqrt N := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' N
  have hbound : (N : ℝ) ≤ 4 * (Nat.sqrt N : ℝ) ^ 2 := by nlinarith
  have hlog := Real.log_le_log hNpos hbound
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (by linarith)), Real.log_pow] at hlog
  norm_num at hlog
  linarith

theorem eventually_probability_log_budget : ∀ᶠ N : ℕ in atTop,
    2 * Real.log (squareScale N : ℝ) + Real.log (shortWidth N : ℝ) +
      111 * probabilityParameter N * Real.log (mixingBase N : ℝ) ≤
        Real.log (Nat.sqrt N : ℝ) := by
  filter_upwards [eventually_logarithmicCeiling_pow_le_scaleBase 20,
    log_scaleBase_div_log_tendsto_zero.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 60010)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    log_nat_tendsto_atTop.eventually (eventually_ge_atTop (2 : ℝ)),
    log_nat_tendsto_atTop.eventually (eventually_ge_atTop (3 * Real.log 4)),
    eventually_ge_atTop 1] with N hW hratio hS hL2 hL4 hN
  have hL : 0 < Real.log (N : ℝ) := by linarith
  have hsmall : 6001 * Real.log (scaleBase N : ℝ) ≤ Real.log (N : ℝ) / 10 := by
    have h := (div_le_iff₀ hL).mp hratio.le
    linarith
  have hWpos := (shortWidth_log_bound hN hL2).1
  have hlogW : Real.log (shortWidth N : ℝ) ≤ Real.log (scaleBase N : ℝ) :=
    Real.log_le_log (by exact_mod_cast hWpos) (by exact_mod_cast hW)
  have hterm : 111 * probabilityParameter N * Real.log (mixingBase N : ℝ) =
      (111 / 1000 : ℝ) * Real.log (N : ℝ) := by
    rw [probabilityParameter, mixingBase, Nat.cast_pow, Real.log_pow]
    push_cast
    field_simp
    norm_num
  have hroot := log_nat_sqrt_lower hN hL4
  rw [hterm, squareScale, Nat.cast_pow, Real.log_pow]
  push_cast
  linarith

theorem eventually_probability_scale_thresholds (T₀ d₀ P₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      T₀ ≤ mixingBase N ∧ 1 < replacementScale N ∧ 2 ≤ cofactorScale N ∧
      2 ^ d₀ < cofactorScale N ∧ 2 * mixingBase N ^ 90 ≤ cofactorScale N ∧
      max P₀ (128 * primeBoxEnlargement 10 * replacementScale N) ≤ cofactorScale N := by
  filter_upwards [scaleBase_tendsto_atTop.eventually
    (eventually_ge_atTop (max (max (max T₀ P₀) (2 ^ d₀ + 1))
      (max 2 (128 * primeBoxEnlargement 10))))] with N hS
  have hT : T₀ ≤ scaleBase N := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hS))
  have hP : P₀ ≤ scaleBase N := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hS))
  have hd : 2 ^ d₀ < scaleBase N := lt_of_lt_of_le (Nat.lt_succ_self _)
    ((le_max_right _ _).trans ((le_max_left _ _).trans hS))
  have hS2 : 2 ≤ scaleBase N := (le_max_left _ _).trans ((le_max_right _ _).trans hS)
  have hC : 128 * primeBoxEnlargement 10 ≤ scaleBase N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hS)
  have hS1 := one_le_scaleBase N
  refine ⟨hT.trans (scaleBase_le_pow N 10 (by decide)),
    (by exact lt_of_lt_of_le (by omega : 1 < scaleBase N) (scaleBase_le_pow N 910 (by decide))),
    hS2.trans (scaleBase_le_pow N 920 (by decide)),
    hd.trans_le (scaleBase_le_pow N 920 (by decide)), ?_, ?_⟩
  · change 2 * (scaleBase N ^ 10) ^ 90 ≤ scaleBase N ^ 920
    rw [← pow_mul]
    calc
      2 * scaleBase N ^ (10 * 90) ≤ scaleBase N ^ 20 * scaleBase N ^ 900 := by
        gcongr
        exact hS2.trans (scaleBase_le_pow N 20 (by decide))
      _ = scaleBase N ^ 920 := by rw [← pow_add]
  · apply max_le
    · exact hP.trans (scaleBase_le_pow N 920 (by decide))
    · change 128 * primeBoxEnlargement 10 * scaleBase N ^ 910 ≤ scaleBase N ^ 920
      calc
        _ ≤ scaleBase N ^ 10 * scaleBase N ^ 910 := by
          gcongr
          exact hC.trans (scaleBase_le_pow N 10 (by decide))
        _ = _ := by rw [← pow_add]

end Erdos380
