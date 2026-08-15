/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Proposition4
import ErdosProblems.Erdos285.Proposition6Final

/-!
# Erdős 285: unconditional final upper construction

This module applies the abstract Proposition 4 assembly to the unconditional
Proposition 6 certificate stream at `ScoreCrossing.martinSelectedScale`.
The resulting cutoff is indexed by the formal problem's parameter `k`, hence
uses the selected scale for the requested cardinality `k + 1`.
-/

namespace Erdos285.MartinUpperFinal

open Filter
open scoped Topology

noncomputable section

/-- Martin's selected denominator cutoff for the formal problem's `k + 1`
term indexing. -/
def martinCutoff (k : ℕ) : ℕ :=
  Proposition4.indexedCutoff ScoreCrossing.martinSelectedScale k

/-- The unconditional upper half of Martin's Proposition 4: sufficiently
large `k` possess an exact `k + 1` term Egyptian-fraction representation whose
denominators are bounded by `martinCutoff k`, and this cutoff has the optimal
asymptotic ratio. -/
theorem martinUpperConclusion :
    (∀ᶠ k : ℕ in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (martinCutoff k) A) ∧
    Tendsto
      (fun k : ℕ ↦ (martinCutoff k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds Analytic.densityConstant) := by
  simpa only [martinCutoff] using
    Proposition4.propositionFour_of_approximationCertificates
      ScoreCrossing.martinSelectedScale
      ScoreCrossing.martinSelectedScale_ratio_tendsto
      eventually_martinApproximationCertificate

/-- The unconditional eventual finite-set witness stream. -/
theorem eventually_martinUpperWitness :
    ∀ᶠ k : ℕ in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (martinCutoff k) A :=
  martinUpperConclusion.1

/-- Martin's selected cutoff divided by the requested number of terms tends
to `e / (e - 1)`. -/
theorem martinCutoff_ratio_tendsto :
    Tendsto
      (fun k : ℕ ↦ (martinCutoff k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds Analytic.densityConstant) :=
  martinUpperConclusion.2

end

end Erdos285.MartinUpperFinal

#print axioms Erdos285.MartinUpperFinal.martinUpperConclusion
#print axioms Erdos285.MartinUpperFinal.eventually_martinUpperWitness
#print axioms Erdos285.MartinUpperFinal.martinCutoff_ratio_tendsto
