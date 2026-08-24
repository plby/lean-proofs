/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.AlmostPrimeExhaustion
import ErdosProblems.Erdos387.Endpoint
import ErdosProblems.Erdos387.QualitativeRoughCounting

namespace Erdos387

theorem not_erdos_387
    (h : ∀ B K : ℕ, 3 ≤ B →
      ∀ S : CoverBPZ.BPZSection6Input B K,
        ∃ X z y medium large secondMin gap : ℕ,
          2 ≤ y ∧ 1 ≤ secondMin ∧
          B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2 ∧
          B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2 ∧
          (CoverBPZ.RefinedLargeErrors S X z large).card +
              (CoverBPZ.RefinedMediumErrors S X z medium large).card +
              (CoverBPZ.RefinedConvenientErrors S X z y medium).card +
              (CoverBPZ.RefinedComparablePrimeErrors S X z secondMin gap
                medium).card +
              (CoverBPZ.RefinedSeparatedAlmostPrimeErrors S X z y medium
                secondMin gap).card <
            (RefinedSiftedCandidates S X z).card) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

end Erdos387
