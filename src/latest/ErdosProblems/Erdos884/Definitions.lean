/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 884.
Informal proof: Daniel Larsen, building on Terence Tao's construction.
Formal proof: Claude Fable 5, with minor guidance from R. J. Honicky.
Source: https://www.erdosproblems.com/884#post-7362
https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258
Original Lean/Mathlib version: 4.31.0.
Original Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The port reuses the repository's existing PNT+ Selberg sieve by Arend Mellendijk.
-/
import Mathlib

namespace Erdos884

noncomputable abbrev sumDivisorInvPairwiseDifference (n : ℕ) : ℝ :=
    ∑ j : Fin n.divisors.card, ∑ i : Fin j,
    (1 : ℚ) / (Nat.nth (· ∣ n) j - Nat.nth (· ∣ n) i)

noncomputable abbrev sumDivisorInvConsecutiveDifference (n : ℕ) : ℝ :=
    ∑ i : Fin (n.divisors.card - 1),
    (1 : ℚ) / (Nat.nth (· ∣ n) (i + 1) - Nat.nth (· ∣ n) i)

end Erdos884
