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

def erdos_367 : Prop :=
  ∀ k ≥ 1, ∃ C : ℝ, ∀ n : ℕ,
    (∏ m ∈ Finset.Ico n (n + k), (powerfulPart m : ℝ)) ≤
      C * (n : ℝ) * (n : ℝ)
end Erdos367b

open scoped Classical in
theorem Erdos367b.disproof_367 :
    Not Erdos367b.erdos_367
  := by
  sorry
