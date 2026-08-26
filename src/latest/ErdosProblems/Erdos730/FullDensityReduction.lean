/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.AnalyticInputs
import ErdosProblems.Erdos730.ConsecutiveTransition
import ErdosProblems.Erdos730.DominatedLimit
import ErdosProblems.Erdos730.FixedDepthParity
import ErdosProblems.Erdos730.FullDensityBudget
import ErdosProblems.Erdos730.FullDensityCore
import ErdosProblems.Erdos730.HigherPowerCount
import ErdosProblems.Erdos730.KummerTransition
import ErdosProblems.Erdos730.ObstructionMaps
import ErdosProblems.Erdos730.PadicIsometry
import ErdosProblems.Erdos730.PositiveDensityBridge

/-!
# Erdős 730: explicit positive-density reduction

This module isolates the explicit quantified density claim and proves, without
any extra axiom, that it implies the exact upstream infinitude target.  The
statement deliberately uses the explicit family from `Erdos730FullDensityCore`;
it is not a theorem-strength placeholder over an arbitrary sequence.

Historically this claim was the final intake boundary.  It is now discharged
unconditionally in `Erdos730FullDensityTheorem`, after formalizing the
Kummer, Mertens, fixed-modulus PNT-in-progressions, and counting arguments.
-/

open Filter

namespace Erdos730
namespace FullDensityReduction

open FullDensityCore

noncomputable section

local instance : DecidablePred GoodParameter :=
  fun _ => Classical.propDecidable _

/-- The explicit quantified density claim used by the historical reduction.

It says that more than `107/2500` of the positive integer parameters in the
four-linear-form family give equal prime support for the two consecutive
central binomial coefficients, in lower-density liminf. -/
def CandidatePositiveDensityClaim : Prop :=
  FullDensity.HasCandidatePositiveDensity GoodParameter

/-- Expanded form of the density claim, useful for hostile audit. -/
theorem candidatePositiveDensityClaim_iff :
    CandidatePositiveDensityClaim ↔
      (107 : ℝ) / 2500 <
        liminf (fun X : ℕ =>
          (((Finset.Icc 1 X).filter GoodParameter).card : ℝ) / X) atTop := by
  rfl

/-- The exact density claim gives infinitely many good parameters. -/
theorem goodParameters_infinite_of_candidatePositiveDensity
    (h : CandidatePositiveDensityClaim) : GoodParameters.Infinite := by
  exact FullDensity.parameterSet_infinite_of_candidatePositiveDensity
    GoodParameter (by simpa [CandidatePositiveDensityClaim] using h)

/-- Kernel-clean final reduction to the exact upstream Erdős 730 set.

No analytic theorem is hidden here: the only hypothesis is the fully expanded
positive-density claim above. -/
theorem pairSet_infinite_of_candidatePositiveDensity
    (h : CandidatePositiveDensityClaim) : PairSet.Infinite := by
  exact pairSet_infinite_of_goodParameters_infinite
    (goodParameters_infinite_of_candidatePositiveDensity h)

/-- The checked numerical node used by the supplied density argument. -/
theorem supplied_density_budget_certificate :
    4 * densityBudgetSeries + (2 / 3) * Real.log 2 < (2393 : ℝ) / 2500 :=
  densityBudget_final_lt

#print axioms candidatePositiveDensityClaim_iff
#print axioms goodParameters_infinite_of_candidatePositiveDensity
#print axioms pairSet_infinite_of_candidatePositiveDensity
#print axioms supplied_density_budget_certificate

end

end FullDensityReduction
end Erdos730
