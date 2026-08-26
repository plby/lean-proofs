import ErdosProblems.Erdos421.WeightedPrimeLogSaving
import ErdosProblems.Erdos421.InverseLogPrimeWeights

/-! # Uniform logarithmic-integral asymptotics for actual prime interval counts -/

namespace Erdos421

open MeasureTheory

theorem prime_interval_logarithmic_integral {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ a b : ℝ, X₀ ≤ a → a ≤ b →
      |((primesInRealInterval a b).card : ℝ) - (∫ t in a..b, (Real.log t)⁻¹)| ≤
        ε * b / (Real.log a) ^ A := by
  obtain ⟨X₁, hX₁, hmean⟩ := prime_log_weighted_log_saving hA
    (by positivity : 0 < ε / 3)
  refine ⟨max X₁ (Real.exp 1 + 1), hX₁.trans_le (le_max_left _ _), ?_⟩
  intro a b ha hab
  have haX : X₁ ≤ a := (le_max_left _ _).trans ha
  have hae : Real.exp 1 + 1 ≤ a := (le_max_right _ _).trans ha
  have ha1 : 1 < a := hX₁.trans_le haX
  have hap : 0 < a := by linarith
  have hbp : 0 < b := hap.trans_le hab
  have hlogp := Real.log_pos ha1
  have hlog1 : 1 ≤ Real.log a := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ a by linarith)
    simpa only [Real.log_exp] using h
  obtain ⟨hf, hf'⟩ := inverse_log_regular (b := b) ha1
  have hm := hmean a b haX hab (fun t ↦ (Real.log t)⁻¹) hf hf'
  rw [inverse_log_prime_sum_eq_card] at hm
  have hnorm := inverse_log_weight_norm_le ha1 hab hlog1
  have hnorm' : b * |(Real.log b)⁻¹| + a * |(Real.log a)⁻¹| +
      (∫ t in a..b, t * |deriv (fun x ↦ (Real.log x)⁻¹) t|) ≤ 3 * b :=
    hnorm.trans (div_le_self (by positivity) hlog1)
  calc
    _ ≤ _ := hm
    _ ≤ (ε / 3 / (Real.log a) ^ A) * (3 * b) :=
      mul_le_mul_of_nonneg_left hnorm' (by positivity)
    _ = _ := by ring

end Erdos421
