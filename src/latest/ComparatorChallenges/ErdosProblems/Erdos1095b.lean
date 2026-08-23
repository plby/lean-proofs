/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1095b

open Filter Real

open scoped Asymptotics Topology

def Good (k n : ℕ) : Prop :=
  k + 1 < n ∧ k < Nat.minFac (Nat.choose n k)
open Classical in
noncomputable def g (k : ℕ) : ℕ :=
  if h : ∃ n : ℕ, Good k n then Nat.find h else 0
end Erdos1095b

open Filter Real
open scoped Asymptotics Topology

namespace Erdos1095b

open scoped Classical in
theorem erdos_1095_weaker_upper_bound :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ k, 2 ≤ k → g k ≤ exp (k ^ (1 + f k)) := by
  sorry

end Erdos1095b
