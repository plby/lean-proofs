/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

namespace Erdos367b

def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n
open Classical in
noncomputable def powerfulPart (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n.divisors.filter IsPowerful).max.getD 1

end Erdos367b

theorem Erdos367b.not_erdos_367 :
    Not (∀ k ≥ 1, ∃ C : ℝ, ∀ n : ℕ,
      (∏ m ∈ Finset.Ico n (n + k), (Erdos367b.powerfulPart m : ℝ)) ≤
        C * (n : ℝ) * (n : ℝ)) := by
  sorry
