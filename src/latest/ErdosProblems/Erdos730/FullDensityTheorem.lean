/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.DivisorSwitching
import ErdosProblems.Erdos730.FullDensityReduction
import ErdosProblems.Erdos730.HigherPowerEvents
import ErdosProblems.Erdos730.RangeAssembly
import ErdosProblems.Erdos730.SmallPrimeEvents

/-!
# Erdős 730: unconditional positive density and infinitude

This file is the terminal assembly of the four disjoint obstruction ranges.
The higher-power and transition ranges tend to zero, the fixed-depth plus
uniform-tail argument bounds the small-prime range, and fixed-modulus divisor
switching bounds the top-prime range.  The exact density budget then gives
positive lower density in the explicit four-linear-form family and hence the
upstream infinitude statement.
-/

open Filter
open scoped Topology

namespace Erdos730.FullDensityTheorem

open Erdos730

/-- The explicit family has lower density strictly greater than `107 / 2500`.
This discharges the former final hypothesis in
`Erdos730FullDensityReduction`. -/
theorem candidatePositiveDensity :
    FullDensityReduction.CandidatePositiveDensityClaim := by
  exact RangeAssembly.hasCandidatePositiveDensity_of_range_estimates
    HigherPowerEvents.tendsto_normalizedHigherPowerWitnessCount_zero
    SmallPrimeEvents.normalizedSmallPrimeWitnessCount_isBoundedUnder
    SmallPrimeEvents.limsup_normalizedSmallPrimeWitnessCount_le
    DivisorSwitching.normalizedTopPrimeWitnessCount_isBoundedUnder
    DivisorSwitching.limsup_normalizedTopPrimeWitnessCount_le

/-- **Erdős #730.**  There are infinitely many consecutive pairs whose
central binomial coefficients have identical prime support. -/
theorem pairSet_infinite : FullDensityCore.PairSet.Infinite := by
  exact FullDensityReduction.pairSet_infinite_of_candidatePositiveDensity
    candidatePositiveDensity

#print axioms candidatePositiveDensity
#print axioms pairSet_infinite

end Erdos730.FullDensityTheorem
