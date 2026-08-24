/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Real
open scoped Topology

namespace Erdos1095b

def Good (k n : ℕ) : Prop :=
  k + 1 < n ∧ k < Nat.minFac (Nat.choose n k)
open Classical in
noncomputable def g (k : ℕ) : ℕ :=
  if h : ∃ n : ℕ, Good k n then Nat.find h else 0

theorem erdos_1095 :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ k, 2 ≤ k → g k ≤ exp (k ^ (1 + f k)) := by
  sorry

end Erdos1095b
