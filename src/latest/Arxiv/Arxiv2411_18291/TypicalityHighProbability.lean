import Arxiv.Arxiv2411_18291.FiniteTypicalityProbability

/-!
# Corrected high-probability typicality

At the paper's density and error scales, the actual failure probability
is smaller than `exp(-n^(1/10))` above an explicit threshold. These eventual
interfaces use that finite theorem. The printed `exp(-n/10)` rate is false,
as verified in `PrintedWhpCounterexample`.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_typical_failure_paper_scales (r h : ℕ) (hh : 1 ≤ h) :
    ∀ᶠ n : ℕ in atTop, ∀ p : unitInterval, (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p →
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
          IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)} ≤
        2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
          Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ) / 12)) := by
  filter_upwards [eventually_ge_atTop (correctedTypicalityThreshold r h)] with n hn
  exact typical_failure_probability_paper_scales_explicit hn hh

theorem eventually_typical_tail_lt_stretched_exp (r h : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
          Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ) / 12)) <
        Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  filter_upwards [eventually_ge_atTop (correctedTypicalityThreshold r h)] with n hn
  exact corrected_typicality_tail hn

theorem eventually_typical_failure_stretched_exp (r h : ℕ) (hh : 1 ≤ h) :
    ∀ᶠ n : ℕ in atTop, ∀ p : unitInterval, (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p →
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
          IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)} <
        Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  filter_upwards [eventually_ge_atTop (correctedTypicalityThreshold r h)] with n hn
  exact typical_failure_stretched_exp_explicit hn hh

/-- The eventual interface to the explicit corrected Lemma 5.3. -/
theorem eventually_typical_paper_whp_corrected (r h : ℕ) (hh : 1 ≤ h) :
    ∀ᶠ n : ℕ in atTop, ∀ p : unitInterval, (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p →
      1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
        (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
          {ω | |density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
            IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h} := by
  filter_upwards [eventually_ge_atTop (correctedTypicalityThreshold r h)] with n hn
  exact typical_paper_whp_corrected_explicit hn hh

end Arxiv2411_18291
