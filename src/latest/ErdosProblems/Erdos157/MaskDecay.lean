import ErdosProblems.Erdos157.MaskTargetCounts

/-! Summable failure probabilities for all mask targets simultaneously. -/

namespace Erdos157.Elementary

open Filter
open scoped Topology

theorem sixth_div_le_trial_exponent (x d : ℝ) (hx : 0 ≤ x) (hd : 0 < d)
    (hupper : d ≤ x ^ 2) : x ^ 6 / 1024 ≤ x ^ 12 / (1024 * d ^ 3) := by
  apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
  have hp : x ^ 6 * d ^ 3 ≤ x ^ 12 := by
    calc
      _ ≤ x ^ 6 * (x ^ 2) ^ 3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hd.le hupper 3) (by positivity)
      _ = _ := by ring
  nlinarith

theorem eventually_quadratic_sub_sixth_le_neg (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, C * (k : ℝ) ^ 2 - (k : ℝ) ^ 6 / 1024 ≤ -(k : ℝ) := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by decide : (4 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (1024 * (C + 1))),
    eventually_ge_atTop 1] with k hk h1
  have h1' : (1 : ℝ) ≤ k := by exact_mod_cast h1
  have hm := mul_le_mul_of_nonneg_right hk (sq_nonneg (k : ℝ))
  have he : (k : ℝ) ^ 4 * (k : ℝ) ^ 2 = (k : ℝ) ^ 6 := by ring
  rw [he] at hm
  nlinarith

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable def MaskLevelFailure (k : ℕ) (τ : LevelMasks K k) : Prop :=
  ∃ z : MaskTarget K k, ¬ MaskTargetHit K τ z

theorem eventually_maskLevelFailure_density :
    ∀ᶠ k in atTop, finiteDensity (MaskLevelFailure K k) ≤ Real.exp (-(k : ℝ)) := by
  classical
  let C : ℝ := Real.log (Fintype.card K) + 6 * Real.log 7
  filter_upwards [eventually_good_extensions (K := K), eventually_ge_atTop 4,
    eventually_quadratic_sub_sixth_le_neg C] with k hg hk hdecay
  let h := prefixLength k
  let ε : ℝ := 1 / (1024 * (levelDegree k : ℝ) ^ 3)
  have hn : 1 ≤ k ^ 12 := Nat.one_le_pow _ _ (by omega)
  have htarget (z : MaskTarget K k) :
      finiteDensity (fun τ : LevelMasks K k => ¬ MaskTargetHit K τ z) ≤
        Real.exp (-((k ^ 12 : ℕ) : ℝ) * ε) :=
    maskTarget_failure_density_le K z hg.1 hn (trialCount_le_pow_prefixLength k) ε
      (good_log_extensions_density K hg.1 (hg.2 hg.1))
  have hdpos : (0 : ℝ) < levelDegree k := by
    have hl := levelDegree_lower k
    have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hdle : (levelDegree k : ℝ) ≤ (k : ℝ) ^ 2 := by
    have hb := double_levelDegree_lt_square k hk
    have hnle : levelDegree k ≤ k ^ 2 := by omega
    exact_mod_cast hnle
  have hratio := sixth_div_le_trial_exponent (k : ℝ) (levelDegree k)
    (Nat.cast_nonneg _) hdpos hdle
  have hexp : Real.exp (-((k ^ 12 : ℕ) : ℝ) * ε) ≤ Real.exp (-(k : ℝ) ^ 6 / 1024) := by
    apply Real.exp_le_exp.mpr
    dsimp only [ε]
    push_cast
    calc
      _ = -((k : ℝ) ^ 12 / (1024 * (levelDegree k : ℝ) ^ 3)) := by ring
      _ ≤ -((k : ℝ) ^ 6 / 1024) := neg_le_neg hratio
      _ = _ := by ring
  calc
    _ ≤ (Fintype.card (MaskTarget K k) : ℝ) * Real.exp (-((k ^ 12 : ℕ) : ℝ) * ε) :=
      finiteDensity_exists_le _ _ htarget
    _ ≤ Real.exp (C * (k : ℝ) ^ 2) * Real.exp (-(k : ℝ) ^ 6 / 1024) :=
      mul_le_mul (card_maskTarget_le_exp K k (by omega)) hexp (by positivity) (by positivity)
    _ = Real.exp (C * (k : ℝ) ^ 2 - (k : ℝ) ^ 6 / 1024) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.mpr hdecay

end Erdos157.Elementary
