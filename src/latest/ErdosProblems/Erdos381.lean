import ErdosProblems.Erdos381.Nicolas

/-!
# Erdős Problem 381

This is the public entry point for the complete formalization of the negative
answer to Erdős Problem 381.  The underlying definitions and elementary
properties are in `Erdos381.Core`; the analytic prime-window estimates and the
Nicolas-type polynomial upper bound are split into the imported helper modules.
-/

open Filter Asymptotics

namespace Erdos381

/-- Nicolas's polynomial upper bound disproves Erdős's proposed universal
logarithmic lower bound for the number of highly composite integers. -/
theorem not_erdos_381 :
    ¬ ∀ k : ℕ, 1 ≤ k →
      (fun n : ℕ => Real.log (n : ℝ) ^ k) =O[atTop]
        (fun n : ℕ => (Q n : ℝ)) := by
  simpa [Erdos381Claim, LogPowerLower, logPower] using not_erdos381Claim

end Erdos381

#print axioms Erdos381.not_erdos_381
