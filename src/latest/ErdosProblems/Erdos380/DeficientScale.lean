import ErdosProblems.Erdos380.DeficientCofactors
import ErdosProblems.Erdos380.ParameterGrowth

/-! # Negligible anchors with deficient cofactors -/

open Filter
open scoped Topology BigOperators

namespace Erdos380

lemma eventually_const_mul_log_scaleBase_pow_le (C a : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, C * (1 + a * Real.log (scaleBase N : ℝ)) ^ m ≤ scaleBase N := by
  filter_upwards [eventually_scaleBase_pow_le 1, eventually_log_pow_le_scaleBase (m + 1),
    log_nat_tendsto_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    log_nat_tendsto_atTop.eventually (eventually_ge_atTop (C * (1 + a) ^ m))]
      with N hSN hpow hL hCbig
  have hS1 : (1 : ℝ) ≤ scaleBase N := by exact_mod_cast one_le_scaleBase N
  have hSpos : (0 : ℝ) < scaleBase N := by linarith
  have hs0 : 0 ≤ Real.log (scaleBase N : ℝ) := Real.log_nonneg hS1
  have hsL : Real.log (scaleBase N : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hSpos (by exact_mod_cast (by simpa only [pow_one] using hSN))
  have hbase : 1 + a * Real.log (scaleBase N : ℝ) ≤ (1 + a) * Real.log (N : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hsL ha
    nlinarith
  calc
    C * (1 + a * Real.log (scaleBase N : ℝ)) ^ m ≤ C * ((1 + a) * Real.log (N : ℝ)) ^ m := by gcongr
    _ = (C * (1 + a) ^ m) * Real.log (N : ℝ) ^ m := by rw [mul_pow]; ring
    _ ≤ Real.log (N : ℝ) * Real.log (N : ℝ) ^ m := mul_le_mul_of_nonneg_right hCbig (by positivity)
    _ = Real.log (N : ℝ) ^ (m + 1) := (pow_succ' _ _).symm
    _ ≤ scaleBase N := hpow

theorem eventually_cofactorDeficientSingletons_scale_bound : ∀ᶠ N : ℕ in atTop,
    ((cofactorDeficientSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100) 9).card : ℝ) ≤
      (N : ℝ) / (scaleBase N : ℝ) ^ 2005 := by
  filter_upwards [eventually_smoothCount_div_scale_upper (k := 920) (r := 1086)
      (by norm_num) (by norm_num) 12100,
    eventually_const_mul_log_scaleBase_pow_le 2 1100 (by norm_num) (by norm_num) 9]
      with N hbound hlog
  have hS1 := one_le_scaleBase N
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast (by omega : 0 < scaleBase N)
  have h := cofactorDeficientSingletons_card_bound (N := N) (Q := scaleBase N ^ 920)
    (Y := scaleBase N ^ 1100) (k := 9) (F := (scaleBase N : ℝ) ^ 1086)
    (one_le_pow₀ hS1) (one_le_pow₀ hS1) (pow_pos hSpos 1086) ?_
  · apply h.trans
    calc
      2 * (N : ℝ) / (scaleBase N ^ 920 : ℕ) / (scaleBase N : ℝ) ^ 1086 *
          (1 + Real.log (scaleBase N ^ 1100 : ℕ)) ^ 9 =
          ((N : ℝ) / (scaleBase N : ℝ) ^ 2006) *
            (2 * (1 + 1100 * Real.log (scaleBase N : ℝ)) ^ 9) := by
        rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, div_div, ← pow_add]
        norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
        ring
      _ ≤ ((N : ℝ) / (scaleBase N : ℝ) ^ 2006) * scaleBase N :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (N : ℝ) / (scaleBase N : ℝ) ^ 2005 := by
        rw [show 2006 = 2005 + 1 from rfl, pow_succ]
        field_simp
  · intro p hp f hf
    have hppos : 0 < p := lt_of_lt_of_le (pow_pos (by omega : 0 < scaleBase N) 920) (Finset.mem_Icc.mp hp).1
    have hdpos : 0 < p ^ 2 * ∏ i, f i := mul_pos (pow_pos hppos 2) (positiveFactorTuples_prod_pos hf)
    have hdsize : p ^ 2 * (∏ i, f i) ≤ scaleBase N ^ 12100 := by
      calc
        p ^ 2 * (∏ i, f i) ≤ (scaleBase N ^ 1100) ^ 2 * (scaleBase N ^ 1100) ^ 9 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (Finset.mem_Icc.mp hp).2 2) (positiveFactorTuples_prod_le hf)
        _ = scaleBase N ^ 12100 := by rw [← pow_add, ← pow_mul]
    exact hbound (p ^ 2 * ∏ i, f i) hdpos hdsize

end Erdos380
