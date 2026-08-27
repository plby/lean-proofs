/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.ResidualPrimeFiberTail
import ErdosProblems.Erdos4b.SingletonAsymptotics
import ErdosProblems.Erdos4b.GeneralFourierDoubledComparison
import ErdosProblems.Erdos4b.GeneralFourierEulerProduct
import ErdosProblems.Erdos4b.GeneralFourierProfile
import ErdosProblems.Erdos4b.GeneralFourierPrimeMass
import ErdosProblems.Erdos4b.GeneralFourierArithmeticEuler
import ErdosProblems.Erdos4b.GeneralFourierFullIntegral
import ErdosProblems.Erdos4b.GeneralFourierRelativeLimit
import ErdosProblems.Erdos4b.GeneralFourierFactorization
import ErdosProblems.Erdos4b.GeneralFourierSingularLowerBound
import ErdosProblems.Erdos4b.GeneralFourierSquareRootCutoff
import ErdosProblems.Erdos4b.GeneralFourierProfileAsymptotic
import ErdosProblems.Erdos4b.GeneralFourierAffineAsymptotic
import ErdosProblems.Erdos4b.GeneralFourierReindex
import ErdosProblems.Erdos4b.GeneralFourierTensorMainConstant
import ErdosProblems.Erdos4b.GeneralFourierPhysicalDensity
import ErdosProblems.Erdos4b.GeneralFourierFiniteNormalization
import ErdosProblems.Erdos4b.GeneralFourierEndpointMass
import ErdosProblems.Erdos4b.GeneralFourierNormalizedEndpoint
import ErdosProblems.Erdos4b.GeneralFourierEndpointDecay
import ErdosProblems.Erdos4b.GeneralFourierSourceNormalization
import ErdosProblems.Erdos4b.GeneralFourierSourceAsymptotic
import ErdosProblems.Erdos4b.SourceDyadicNormalization
import ErdosProblems.Erdos4b.GeneralFourierTotientEuler
import ErdosProblems.Erdos4b.GeneralFourierTotientFiniteIntegral
import ErdosProblems.Erdos4b.GeneralFourierTotientSupport
import ErdosProblems.Erdos4b.GeneralFourierTotientFullIntegral
import ErdosProblems.Erdos4b.GeneralFourierL1Bounds
import ErdosProblems.Erdos4b.GeneralFourierTotientProfileAsymptotic
import ErdosProblems.Erdos4b.GeneralFourierTotientCoefficientSquare
import ErdosProblems.Erdos4b.SourceDyadicCommonNormalization
import ErdosProblems.Erdos4b.GeneralFourierPinnedAsymptotic
import ErdosProblems.Erdos4b.GeneralFourierPinnedMultiplicity
import ErdosProblems.Erdos4b.GeneralFourierPinnedFiniteAsymptotic
import ErdosProblems.Erdos4b.GeneralFourierPinnedCoefficientFace
import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightedAsymptotic
import ErdosProblems.Erdos4b.GeneralFourierPinnedMainConstant
import ErdosProblems.Erdos4b.GeneralFourierPinnedSourceAsymptotic
import ErdosProblems.Erdos4b.GeneralFourierPinnedSupportedCompatibility
import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeCount
import ErdosProblems.Erdos4b.GeneralFourierPinnedCoefficientExtension
import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightedPrimeCount
import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightExpansion
import ErdosProblems.Erdos4b.GeneralFourierPinnedModulusFibers
import ErdosProblems.Erdos4b.GeneralFourierPinnedProductSupport
import ErdosProblems.Erdos4b.GeneralFourierPinnedSourceDistribution
import ErdosProblems.Erdos4b.GeneralFourierPinnedDistributionRange
import ErdosProblems.Erdos4b.GeneralFourierPinnedUnconditionalDistribution
import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularLowerBound
import ErdosProblems.Erdos4b.GeneralFourierPinnedTauDecay
import ErdosProblems.Erdos4b.SourcePrimeIntervalLogSaving
import ErdosProblems.Erdos4b.SourcePrimeIntervalLowerBound
import ErdosProblems.Erdos4b.GeneralFourierPinnedNormalizedError
import ErdosProblems.Erdos4b.GeneralFourierPinnedUniformError
import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeAsymptotic
import ErdosProblems.Erdos4b.GeneralFourierPinnedPhysicalWeight
import ErdosProblems.Erdos4b.SourceDyadicPinnedNormalization
import ErdosProblems.Erdos4b.SingularWeightedPrimeAverage
import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedCrt
import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedCompatibility
import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedIncidence
import ErdosProblems.Erdos4b.GeneralFourierForcedPrimeFactor
import ErdosProblems.Erdos4b.GeneralFourierForcedEuler
import ErdosProblems.Erdos4b.GeneralFourierForcedFiniteIntegral
import ErdosProblems.Erdos4b.GeneralFourierForcedSupport
import ErdosProblems.Erdos4b.GeneralFourierForcedProduct
import ErdosProblems.Erdos4b.GeneralFourierForcedFullIntegral
import ErdosProblems.Erdos4b.GeneralFourierTotientL1Bounds
import ErdosProblems.Erdos4b.GeneralFourierForcedIntegralBound
import ErdosProblems.Erdos4b.GeneralFourierPinnedPositiveWeight
import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedUniformError
import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedSourceWeight
import ErdosProblems.Erdos4b.GeneralFourierForcedProfileBound
import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedSourceBound
import ErdosProblems.Erdos4b.GeneralFourierPinnedCollisionLossLimit
import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightedLower
import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularRatioAlgebra
import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularRatios
import ErdosProblems.Erdos4b.GeneralFourierPinnedSmallSingularRatios
import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularMassLower
import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularMassLimit
import ErdosProblems.Erdos4b.SourceDyadicPinnedSingularMass
import ErdosProblems.Erdos4b.SourceDyadicResidueCoverage
import ErdosProblems.Erdos4b.SourceDyadicResidualFiberWeighted
import ErdosProblems.Erdos4b.SourcePrimeIntervalRelativeCount
import ErdosProblems.Erdos4b.SourceIntervalAllocation
import ErdosProblems.Erdos4b.SourceDyadicProxyCoverage
import ErdosProblems.Erdos4b.SourceResidualAllocationCost
import ErdosProblems.Erdos4b.SourceDyadicAllocation
import ErdosProblems.Erdos4b.SourceDyadicAllocatedCoverage
import ErdosProblems.Erdos4b.SourceDyadicBoundaryCount
import ErdosProblems.Erdos4b.SourceDyadicBoundaryBudget
import ErdosProblems.Erdos4b.SourceDyadicTailBudget
import ErdosProblems.Erdos4b.SourceDyadicSmoothBudget
import ErdosProblems.Erdos4b.SourceFreshPrimeReserve
import ErdosProblems.Erdos4b.SourceFiniteCover
import ErdosProblems.Erdos4b.SourceDyadicGlobalCover
import ErdosProblems.Erdos4b.SourceSmoothRectangle
import ErdosProblems.Erdos4b.SourceUnboundedProfiles
import ErdosProblems.Erdos4b.SourceUnconditionalDyadicCovers
import ErdosProblems.Erdos4b.RankinMonotonicity
import ErdosProblems.Erdos4b.RankinDyadicEndpoint
import ErdosProblems.Erdos4b.FGKMTIndexGap

/-!
# Erdős Problem 4: unbounded Rankin constants and the stronger FGKMT18 bound

The proof constructs smooth profiles with unbounded variational quotient,
uses them in the proved sieve and finite probability covering argument,
and transfers the resulting covers to the exact prime-index inequality.

The definition `Erdos4For` in `Base.lean` is the literal statement, with
zero-indexed `Nat.nth Nat.Prime` and real subtraction and logarithms.

The growing-dimensional sieve and finite hypergraph covering argument also
give the stronger FGKMT18 maximal-gap bound, with a single third logarithm
in the denominator, and its exact infinite prime-index corollary below.
-/

namespace Erdos4b

open Filter

/-- For every positive constant, the exact set of prime-gap indices in
Erdős Problem 4 is infinite. -/
theorem erdos4For_pos (C : ℝ) (hC : 0 < C) : Erdos4For C := by
  obtain ⟨a, hcovers⟩ := SmoothParameters.exists_dyadicRay_covers
  obtain ⟨D, hD, hthreshold⟩ := SmoothParameters.exists_dyadicMultiplier_threshold_bound a hC
  apply erdos4For_of_bounded_survivor_cover_data C
  intro N
  let B := max (max 2 (Nat.nth Nat.Prime N)) 1 + 1
  have hB : 0 < B := Nat.succ_pos _
  obtain ⟨r, hrcover, hrthreshold⟩ := ((hcovers D hD).and (hthreshold B hB)).exists
  obtain ⟨data, hyz, hzx, hmeasure, hfresh⟩ := hrcover
  refine ⟨D * SmoothParameters.intervalLength a r, SmoothParameters.smoothFrontier r,
    SmoothParameters.residualPrimeFrontier a r, SmoothParameters.primaryFrontier a r,
    data, hyz, hzx, hmeasure, hfresh, ?_⟩
  intro n _ hn
  exact hrthreshold n hn

/-- The affirmative resolution of Erdős Problem 4. -/
theorem erdos_4_answer : answer(True) ↔ (∀ C > 0, Erdos4For C) := by
  constructor
  · intro _ C hC
    exact erdos4For_pos C hC
  · intro _
    trivial

/-- The exact large-prime-gap statement with its proposition expanded. -/
theorem erdos_4 (C : ℝ) (hC : 0 < C) :
    {n : ℕ | (n + 1).nth Nat.Prime - n.nth Nat.Prime >
      C * Real.log (Real.log n) * Real.log (Real.log (Real.log (Real.log n))) /
        (Real.log (Real.log (Real.log n))) ^ 2 * Real.log n}.Infinite := by
  simpa [Erdos4For] using erdos4For_pos C hC

/-- The stronger FGKMT18 bound holds below every sufficiently large real endpoint.
Both consecutive primes, including the right-hand prime, lie below that endpoint. -/
theorem fgkmt18 :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∃ n : ℕ,
      (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
      c * Real.log X * Real.log (Real.log X) *
        Real.log (Real.log (Real.log (Real.log X))) / Real.log (Real.log (Real.log X)) ≤
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨c, hc, hgap⟩ := FGKMT.exists_eventual_maximal_gap
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hgap
  refine ⟨c, hc, X₀, ?_⟩
  intro X hX
  simpa only [fgkmtScale, mul_div_assoc, mul_assoc] using hX₀ X hX

/-- Infinitely many indices satisfy the stronger bound with a single third-logarithm
factor in the denominator. -/
theorem fgkmt18_index :
    ∃ c : ℝ, 0 < c ∧
      {n : ℕ | (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n >
        c * Real.log (Real.log (n : ℝ)) * Real.log (Real.log (Real.log (Real.log (n : ℝ)))) /
          Real.log (Real.log (Real.log (n : ℝ))) * Real.log (n : ℝ)}.Infinite := by
  simpa only [StrongErdos4For, strongThreshold] using FGKMT.exists_strong_index_gaps

end Erdos4b

#print axioms Erdos4b.erdos_4
#print axioms Erdos4b.fgkmt18
#print axioms Erdos4b.fgkmt18_index
