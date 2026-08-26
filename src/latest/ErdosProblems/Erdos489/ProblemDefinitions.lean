import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Classical Filter
open scoped Topology BigOperators

/-- Positive natural numbers divisible by no member of `A`. -/
def sievedSet (A : Set ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ ∀ a ∈ A, ¬ a ∣ n}

/-- The sum of squared successive gaps whose left endpoint is below `x`. -/
noncomputable def gapSumSq (A : Set ℕ) (x : ℕ) : ℝ :=
  let B := sievedSet A
  let b := Nat.nth (· ∈ B)
  ∑ i ∈ Finset.range (Nat.count (· ∈ B) x),
    ((b (i + 1) : ℝ) - (b i : ℝ)) ^ 2

end Erdos489
