/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform quantitative small-ball estimates at the fine-grid threshold.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.FineGridPowers
import ErdosProblems.Erdos521.MainBinVariance
import ErdosProblems.Erdos521.SmallBallLimits

namespace Erdos521

open MeasureTheory Filter

noncomputable def fineGridSmallBallConstant : ℝ := normalizedSmallBallConstant + 3 * Real.exp (1 / 2)

theorem fineGridSmallBallConstant_pos : 0 < fineGridSmallBallConstant := by
  unfold fineGridSmallBallConstant
  have h := normalizedSmallBallConstant_pos
  positivity

theorem normalizedSmallBallError_le_fineThreshold {j : ℕ} (hj : 0 < j) {V : ℝ}
    (hV₂ : (j : ℝ) ^ 2 ≤ V) (hV₅₀ : 2 * (j : ℝ) ^ 50 ≤ V)
    (hdec₁ : Real.exp (-(1 / (4 * Real.pi ^ 2)) * (j : ℝ) ^ 2) ≤ fineGridThreshold j)
    (hdec₂ : Real.exp (-(j : ℝ) ^ 2) ≤ fineGridThreshold j) :
    normalizedSmallBallError V (fineGridThreshold j) ≤ 3 * Real.exp (1 / 2) * fineGridThreshold j := by
  let c : ℝ := 1 / (4 * Real.pi ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have h₁ : Real.exp (-c * V) ≤ fineGridThreshold j := by
    apply le_trans _ hdec₁
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hV₂ hc.le
    linarith
  have h₂ : Real.exp (-(fineGridThreshold j ^ 2 / 2) * V) ≤ fineGridThreshold j := by
    apply le_trans _ hdec₂
    apply Real.exp_le_exp.mpr
    have h := fineGrid_threshold_variance_lower hj hV₅₀
    nlinarith
  change Real.exp (1 / 2) * (Real.exp (-c * V) + 2 * Real.exp (-(fineGridThreshold j ^ 2 / 2) * V)) ≤ _
  calc
    _ ≤ Real.exp (1 / 2) * (fineGridThreshold j + 2 * fineGridThreshold j) :=
      mul_le_mul_of_nonneg_left (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num))) (Real.exp_pos _).le
    _ = _ := by ring

theorem eventually_mainBin_fine_error :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, ∀ x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)),
      normalizedSmallBallError (geometricVariance x (2 ^ j + 1)) (fineGridThreshold j) ≤
        3 * Real.exp (1 / 2) * fineGridThreshold j := by
  have hV₂ : ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, ∀ x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)),
      (j : ℝ) ^ 2 ≤ geometricVariance x (2 ^ j + 1) := by
    simpa only [one_mul, Real.rpow_two] using eventually_mainBin_variance_ge 1 2
  have hV₅₀ : ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, ∀ x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)),
      2 * (j : ℝ) ^ 50 ≤ geometricVariance x (2 ^ j + 1) := by
    simpa only [Real.rpow_ofNat] using eventually_mainBin_variance_ge 2 50
  have hc : 0 < (1 / (4 * Real.pi ^ 2) : ℝ) := by positivity
  have hdec₁ : ∀ᶠ j : ℕ in atTop,
      Real.exp (-(1 / (4 * Real.pi ^ 2)) * (j : ℝ) ^ 2) ≤ fineGridThreshold j := by
    simpa only [Real.rpow_two, ← fineGridThreshold_eq_rpow] using
      eventually_exp_neg_rpow_le_rpow hc (by norm_num : (0 : ℝ) < 2) (-24)
  have hdec₂ : ∀ᶠ j : ℕ in atTop, Real.exp (-(j : ℝ) ^ 2) ≤ fineGridThreshold j := by
    simpa only [Real.rpow_two, neg_one_mul, ← fineGridThreshold_eq_rpow] using
      eventually_exp_neg_rpow_le_rpow (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2) (-24)
  filter_upwards [hV₂, hV₅₀, hdec₁, hdec₂, eventually_ge_atTop 1] with j hj₂ hj₅₀ hd₁ hd₂ hj
  intro k hk x hx
  exact normalizedSmallBallError_le_fineThreshold (by omega) (hj₂ k hk x hx) (hj₅₀ k hk x hx) hd₁ hd₂

theorem eventually_mainBin_fine_smallBall :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, ∀ x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)),
      sequenceLaw.real {ε | |powerSum ε (2 ^ j + 1) x| ≤
        fineGridThreshold j * Real.sqrt (geometricVariance x (2 ^ j + 1))} ≤
        fineGridSmallBallConstant * fineGridThreshold j := by
  filter_upwards [eventually_mainBin_point_variance, eventually_mainBin_fine_error, eventually_ge_atTop 1]
    with j hj herr hj₁
  intro k hk x hx
  have hp := hj k hk x hx
  have h := powerSum_smallBall_normalized_error (2 ^ j) (by linarith [hp.1] : 1 / 2 ≤ x)
    hp.2.1.le (fineGridThreshold_pos (j := j) (by omega))
  have he := herr k hk x hx
  unfold fineGridSmallBallConstant
  linarith

end Erdos521
