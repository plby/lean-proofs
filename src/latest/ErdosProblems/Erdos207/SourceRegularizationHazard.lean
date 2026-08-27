/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationHazardScale
import ErdosProblems.Erdos207.RandomConfigurationMeanBudgets

/-! # The regularizer's point probability at the exact source exponent -/

namespace Erdos207

open scoped NNReal

theorem regularization_source_probability_le
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (G0 : Finset (Finset I)) (j : ℕ) (hj : 4 ≤ j)
    (hm : 2 * (j - 3) ≤ Fintype.card I) (n sigma C B delta : ℝ≥0)
    (hn : 0 < n) (hsigma : 0 < sigma) (hC : 0 < C)
    (hmass : sigma * n ^ 3 / C ≤ Fintype.card I)
    (hdegree : (finiteHypergraphMaxDegree G0 : ℝ≥0) ≤ B * sigma ^ (j - 3) * n ^ (j - 3))
    (hcoefficient : (2 : ℝ≥0) ^ (j - 1) * (2 * C) ^ (j - 3) * (j - 3).factorial * B ≤ delta) :
    2 * regularizationBaseHazard G0 (j - 2) ≤ sourceRandomConfigurationProbability n delta j := by
  have he : j - 2 - 1 = j - 3 := by omega
  have hjp : j - 2 + 1 = j - 1 := by omega
  have hexp : 2 * (j - 3) = 2 * j - 6 := by omega
  have h := regularizationBaseHazard_le_source_scale G0 (j - 2)
    (by simpa only [he] using hm) n sigma C B hn hsigma hC hmass (by simpa only [he] using hdegree)
  simp only [he, hjp, hexp] at h
  exact h.trans (div_le_div_of_nonneg_right hcoefficient zero_le)

end Erdos207
