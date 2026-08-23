/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators

noncomputable section

namespace Erdos220

open scoped Classical in
def sumSquaredGaps : List ℕ → ℕ
  | a :: b :: rest => (b - a) ^ 2 + sumSquaredGaps (b :: rest)
  | _ => 0

end Erdos220

namespace Erdos220

open scoped Classical in
def sortedTotatives (n : ℕ) : List ℕ :=
  ((Finset.Ico 1 n).filter fun m => m.Coprime n).sort (· ≤ ·)

end Erdos220

namespace Erdos220

open scoped Classical in
theorem erdos_220 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (sumSquaredGaps (sortedTotatives n) : ℝ) ≤
        C * (n : ℝ) ^ 2 / (n.totient : ℝ) := by
  sorry

end Erdos220

end
