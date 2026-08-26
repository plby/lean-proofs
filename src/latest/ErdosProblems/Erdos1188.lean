import ErdosProblems.Erdos1188.Proof

/-!
Colin Snyder and GPT-5.6's formalization of the exponent-scale estimate for
Erdős Problem 1188. See Erdos1188/README.md for source and version details.
-/

namespace Erdos1188

/-- The double logarithm of the number of minimal distinct covering systems
is asymptotic to the logarithm of the modulus cutoff. -/
theorem erdos_1188 :
    Filter.Tendsto (fun x : ℕ =>
      Real.log (Real.log (coveringCount x : ℝ)) / Real.log (x : ℝ))
      Filter.atTop (nhds 1) := by
  exact erdos1188_loglog_ratio_tendsto_one

end Erdos1188

#print axioms Erdos1188.erdos_1188
