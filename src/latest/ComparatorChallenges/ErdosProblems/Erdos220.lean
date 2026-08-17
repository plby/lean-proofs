import Mathlib

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos220

def sumSquaredGaps : List ℕ → ℕ
  | a :: b :: rest => (b - a) ^ 2 + sumSquaredGaps (b :: rest)
  | _ => 0

end Erdos220

namespace Erdos220

def sortedTotatives (n : ℕ) : List ℕ :=
  ((Finset.Ico 1 n).filter fun m => m.Coprime n).sort (· ≤ ·)

end Erdos220

namespace Erdos220

theorem erdos_220 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (sumSquaredGaps (sortedTotatives n) : ℝ) ≤
        C * (n : ℝ) ^ 2 / (n.totient : ℝ) := by
  sorry

end Erdos220

end
