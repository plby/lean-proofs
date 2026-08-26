import Mathlib

namespace Erdos489

/-- Positive integers divisible by no forbidden member. -/
def sievedSet (A : Set ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ ∀ a ∈ A, ¬ a ∣ n}

/-- Sum over every consecutive gap whose left endpoint is strictly below x. -/
noncomputable def gapSumSq (A : Set ℕ) (x : ℕ) : ℝ := by
  classical
  let B := sievedSet A
  let b := Nat.nth (· ∈ B)
  exact ∑ i ∈ Finset.range (Nat.count (· ∈ B) x),
    ((b (i + 1) : ℝ) - (b i : ℝ)) ^ 2

open scoped Classical in
/-- The squared-gap average converges along natural cutoffs. -/
theorem erdos_489_nat (A : Set ℕ)
    (hthin : (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ))
      =o[Filter.atTop] (fun x : ℕ => Real.sqrt (x : ℝ)))
    (hB : (sievedSet A).Infinite) :
    ∃ L : ℝ, Filter.Tendsto (fun x : ℕ => gapSumSq A x / (x : ℝ))
      Filter.atTop (nhds L) := by
  sorry

open scoped Classical in
/-- The original real-cutoff limit. The ceiling keeps exactly the natural
left endpoints strictly below the real cutoff. -/
theorem erdos_489 (A : Set ℕ)
    (hthin : (fun x : ℝ => (((Finset.Icc 1 ⌊x⌋₊).filter (· ∈ A)).card : ℝ))
      =o[Filter.atTop] Real.sqrt)
    (hB : (sievedSet A).Infinite) :
    ∃ L : ℝ, Filter.Tendsto (fun x : ℝ => gapSumSq A ⌈x⌉₊ / x)
      Filter.atTop (nhds L) := by
  sorry

end Erdos489
