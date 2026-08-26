/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos696.Conditional
import ErdosProblems.Erdos696.RealTransfer

/-!
# Erdős Problem 696

For almost all integers, the maximal prime-chain length is asymptotic to
`logStar n / 2`, the maximal divisor-chain length is asymptotic to `logStar n`,
and their ratio tends to two.

The conditional argument linked from
https://www.erdosproblems.com/forum/thread/696#post-6848 is preserved in
`Conditional.lean`. Its remaining Siegel–Walfisz hypothesis is discharged by
`siegelWalfisz_unconditional`, derived from the existing BoundedGaps library.
Mertens and Brun–Titchmarsh are proved in `AnalyticInputs.lean`.

No computational limits are increased in this development.
-/

namespace Erdos696

/-- The unconditional asymptotics for the prime and divisor chains in Problem 696. -/
theorem erdos_696 :
    ∀ ε : ℝ, 0 < ε →
      almostAll (fun n =>
        |(hChain n : ℝ) - (logStar n : ℝ) / 2| ≤ ε * (logStar n : ℝ)) ∧
      almostAll (fun n =>
        |(HChain n : ℝ) - (logStar n : ℝ)| ≤ ε * (logStar n : ℝ)) ∧
      almostAll (fun n =>
          n ≥ 2 → |(HChain n : ℝ) / (hChain n : ℝ) - 2| ≤ ε) := by
  exact erdos_696_of_siegel_walfisz (sw := siegelWalfisz_unconditional)

end Erdos696
