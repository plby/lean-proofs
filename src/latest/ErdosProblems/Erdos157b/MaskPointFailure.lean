import ErdosProblems.Erdos157b.MaskFailure
import ErdosProblems.Erdos157b.PrimeSupply

/-! A uniform bound for a single mask target; no separate infinite mask selection. -/

namespace Erdos157.Binary

open Elementary Filter

theorem fourth_div_le_trial_exponent (x d : ℝ) (hx : 0 ≤ x) (hd : 0 < d)
    (hupper : d ≤ x ^ 2) : x ^ 4 / 1024 ≤ x ^ 10 / (1024 * d ^ 3) := by
  apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
  have hp : x ^ 4 * d ^ 3 ≤ x ^ 10 := by
    calc
      _ ≤ x ^ 4 * (x ^ 2) ^ 3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hd.le hupper 3) (by positivity)
      _ = _ := by ring
  nlinarith

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem eventually_maskTarget_failure :
    ∀ᶠ k in atTop, ∀ z : MaskTarget K k,
      finiteDensity (fun τ : LevelMasks K k => ¬MaskTargetHit K τ z) ≤
        Real.exp (-(k : ℝ) ^ 4 / 1024) := by
  filter_upwards [eventually_good_extensions (K := K), eventually_ge_atTop 4] with k hg hk z
  let ε : ℝ := 1 / (1024 * (levelDegree k : ℝ) ^ 3)
  have hn : 1 ≤ trialCount k := Nat.one_le_pow _ _ (by omega)
  have htarget := maskTarget_failure_density_le K z hg.1 hn
    (fun i hi => enough_high_tags k i hi) ε
    (good_log_extensions_density K hg.1 (hg.2 hg.1))
  have hdpos : (0 : ℝ) < levelDegree k := by
    have hl := levelDegree_lower k
    have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hdle : (levelDegree k : ℝ) ≤ (k : ℝ) ^ 2 := by
    have hb := double_levelDegree_lt_square k hk
    have hnle : levelDegree k ≤ k ^ 2 := by omega
    exact_mod_cast hnle
  apply htarget.trans
  apply Real.exp_le_exp.mpr
  have hratio := fourth_div_le_trial_exponent (k : ℝ) (levelDegree k)
    (Nat.cast_nonneg _) hdpos hdle
  dsimp only [ε, trialCount]
  push_cast
  calc
    _ = -((k : ℝ) ^ 10 / (1024 * (levelDegree k : ℝ) ^ 3)) := by ring
    _ ≤ -((k : ℝ) ^ 4 / 1024) := neg_le_neg hratio
    _ = _ := by ring

end Erdos157.Binary
