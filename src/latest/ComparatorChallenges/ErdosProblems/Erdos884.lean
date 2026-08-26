/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0.
Definitions adapted from the upstream formalization; modified for this repository. -/
import Mathlib

namespace Erdos884

noncomputable abbrev sumDivisorInvPairwiseDifference (n : ℕ) : ℝ :=
    ∑ j : Fin n.divisors.card, ∑ i : Fin j,
    (1 : ℚ) / (Nat.nth (· ∣ n) j - Nat.nth (· ∣ n) i)

noncomputable abbrev sumDivisorInvConsecutiveDifference (n : ℕ) : ℝ :=
    ∑ i : Fin (n.divisors.card - 1),
    (1 : ℚ) / (Nat.nth (· ∣ n) (i + 1) - Nat.nth (· ∣ n) i)

theorem not_erdos_884 :
    ¬ (sumDivisorInvPairwiseDifference =O[Filter.atTop]
      (1 + sumDivisorInvConsecutiveDifference)) := by
  sorry

end Erdos884
