/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.Core
import ErdosProblems.Erdos360.FiberCoherence
import ErdosProblems.Erdos360.WeightedGraph
import ErdosProblems.Erdos360.AffineConnector
import ErdosProblems.Erdos360.SharpFiberMass
import ErdosProblems.Erdos360.CarryCompletion
import ErdosProblems.Erdos360.FiniteReduction
import ErdosProblems.Erdos360.GcdNormalization
import ErdosProblems.Erdos360.LargeSubgroup
import ErdosProblems.Erdos360.CyclicInverse
import ErdosProblems.Erdos360.CoarseCyclicInverse
import ErdosProblems.Erdos360.DenseCoreCompletion
import ErdosProblems.Erdos360.ConstantLossInverse
import ErdosProblems.Erdos360.OrdinaryGrowth
import ErdosProblems.Erdos360.CoverSieve
import ErdosProblems.Erdos360.SharpModular
import ErdosProblems.Erdos360.StepBoundedCover
import ErdosProblems.Erdos360.AlmostPeriod
import ErdosProblems.Erdos360.CosetContraction
import ErdosProblems.Erdos360.LowLayerInverse
import ErdosProblems.Erdos360.LowerSieveSet
import ErdosProblems.Erdos360.BadQuotients
import ErdosProblems.Erdos360.StructuredCount
import ErdosProblems.Erdos360.TotientStep
import ErdosProblems.Erdos360.LowerParameters
import ErdosProblems.Erdos360.InitialMertens
import ErdosProblems.Erdos360.CFPModularPhases
import ErdosProblems.Erdos360.AdaptiveSelector
import ErdosProblems.Erdos360.ModularInverseBridge
import ErdosProblems.Erdos360.LevCompletion
import ErdosProblems.Erdos360.RandomDiversity
import ErdosProblems.Erdos360.LowerAnalytic
import ErdosProblems.Erdos360.LowerAssembly
import ErdosProblems.Erdos360.LowerAssemblyNumeric
import ErdosProblems.Erdos360.FiniteSourceAssembly
import ErdosProblems.Erdos360.LevTheorem
import ErdosProblems.Erdos360.PrimePoolSharpEventually

/-!
# Erdős Problem 360

Public entry point for the complete formalization.  The foundational finite,
additive-combinatorial, analytic, and upper-bound development is in
`ErdosProblems.Erdos360.Core`; the lower-bound completion is imported below
as its components are verified.
-/

namespace Erdos360

/-- Erdős Problem 360: the least number of classes needed to partition
`{1, ..., n - 1}` while forbidding a monochromatic distinct-element sum
equal to `n` has the Conlon--Fox--Pham order of growth encoded by
`resolutionScale`. -/
theorem erdos360 : Resolution := by
  obtain ⟨c, hc, hsource⟩ :=
    exists_eventually_controlledPrimeRandomTheorem
  exact resolution_of_controlledPrimeRandom
    hc cfpLevHighMultiplicityPrinciple hsource

/-- The explicit two-sided asymptotic resolution of Erdős Problem 360. -/
theorem erdos_360 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        c * resolutionScale n ≤ (f n : ℝ) ∧
          (f n : ℝ) ≤ C * resolutionScale n :=
  erdos360

#print axioms Erdos360.erdos360
#print axioms Erdos360.erdos_360

end Erdos360
