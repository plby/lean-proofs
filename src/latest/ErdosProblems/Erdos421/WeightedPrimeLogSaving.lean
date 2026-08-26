import ErdosProblems.Erdos421.PrimeWeightedError
import ErdosProblems.Erdos421.ThetaLogSaving

/-! # The quantitative prime number theorem for arbitrary smooth finite weights -/

namespace Erdos421

open MeasureTheory

theorem prime_log_weighted_log_saving {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ a b : ℝ, X₀ ≤ a → a ≤ b → ∀ f : ℝ → ℝ,
      (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) →
      ContinuousOn (deriv f) (Set.Icc a b) →
      |(∑ p ∈ primesInRealInterval a b, f p * Real.log p) - (∫ t in a..b, f t)| ≤
        (ε / (Real.log a) ^ A) *
          (b * |f b| + a * |f a| + ∫ t in a..b, t * |deriv f t|) := by
  obtain ⟨X₀, hX₀, hθ⟩ := chebyshev_theta_log_saving hA hε
  refine ⟨X₀, hX₀, ?_⟩
  intro a b ha hab f hf hf'
  have ha1 : 1 < a := hX₀.trans_le ha
  have hap : 0 < a := by linarith
  have hlog := Real.log_pos ha1
  apply prime_log_weighted_error_le hap.le hab hf hf'
  intro t ht
  have htp : 0 < t := hap.trans_le ht.1
  calc
    _ ≤ ε * t / (Real.log t) ^ A := hθ t (ha.trans ht.1)
    _ ≤ ε * t / (Real.log a) ^ A :=
      div_le_div_of_nonneg_left (mul_nonneg hε.le htp.le) (Real.rpow_pos_of_pos hlog A)
        (Real.rpow_le_rpow hlog.le (Real.log_le_log hap ht.1) hA)
    _ = _ := by ring

end Erdos421
