/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 341: a negative answer by Zhiheng Li with GPT-5.6 Sol.
Source: https://github.com/LiAlreadyExists/Erdos-341
Revision: c1d912189983ac2fa177e7adb1223d4b9ba85e6f (Lean 4.33.0-rc1).
Claim: https://www.erdosproblems.com/forum/thread/341/proof-claims#proof-claim-200
-/
import ErdosProblems.Erdos341.Proof

namespace Erdos341

theorem not_erdos_341 :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 0 < a n) ∧
      (∃ k : ℕ, ∀ n : ℕ, k ≤ n →
        (¬ ∃ i ≤ n, ∃ j ≤ n, a i + a j = a (n + 1)) ∧
        ∀ t : ℕ, a n < t → t < a (n + 1) →
          ∃ i ≤ n, ∃ j ≤ n, a i + a j = t) ∧
      ¬ ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n →
        a (n + p + 1) - a (n + p) = a (n + 1) - a n := by
  refine ⟨enumeration, enumeration_strictMono, ?_, ?_, ?_⟩
  · intro n
    apply S_positive
    simpa [enumeration, enumOf] using Nat.nth_mem_of_infinite S_infinite n
  · obtain ⟨k, _, hk⟩ := least_next_rule_after_fixed_seed
    exact ⟨k, fun n hn => (hk n hn).2⟩
  · change ¬ EventuallyPeriodic gap
    exact gap_not_eventuallyPeriodic

end Erdos341
