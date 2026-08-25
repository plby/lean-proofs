/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
An unconditional Lean formalization of the bounds in tex/587.tex.
https://www.erdosproblems.com/forum/thread/587

Informal authors:
- H. H. Nguyen
- V. H. Vu

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos587.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/587.lean
-/
/- Copyright 2026. Released under Apache 2.0 license. -/

import ErdosProblems.Erdos587.BalancedGeometry
import ErdosProblems.Erdos587.ReciprocalWeyl
import ErdosProblems.Erdos587.ReciprocalPoisson
import ErdosProblems.Erdos587.GaussReciprocity
import ErdosProblems.Erdos587.ReciprocalWeighted
import ErdosProblems.Erdos587.SchwartzWeights
import ErdosProblems.Erdos587.ReciprocalSeries
import ErdosProblems.Erdos587.FresnelSeries
import ErdosProblems.Erdos587.NearbyReciprocity
import ErdosProblems.Erdos587.NearbyMean
import ErdosProblems.Erdos587.FresnelTails
import ErdosProblems.Erdos587.CenteredQuadratic
import ErdosProblems.Erdos587.CenteredMean
import ErdosProblems.Erdos587.ChirpWeights
import ErdosProblems.Erdos587.CenteredSeries
import ErdosProblems.Erdos587.ChirpQuadrature
import ErdosProblems.Erdos587.LowFrequency
import ErdosProblems.Erdos587.ArithmeticBlocks
import ErdosProblems.Erdos587.BlockParameters
import ErdosProblems.Erdos587.HighBlocks
import ErdosProblems.Erdos587.NearbyPartition
import ErdosProblems.Erdos587.NearbyAssembly
import ErdosProblems.Erdos587.NearbyScale
import ErdosProblems.Erdos587.PowerScales
import ErdosProblems.Erdos587.CriticalScale
import ErdosProblems.Erdos587.IteratedCenteredMean
import ErdosProblems.Erdos587.RootMargin
import ErdosProblems.Erdos587.RootDensity
import ErdosProblems.Erdos587.EulerDensity
import ErdosProblems.Erdos587.RootCounts
import ErdosProblems.Erdos587.RootSmallPeriod
import ErdosProblems.Erdos587.OddRootDensity
import ErdosProblems.Erdos587.EvenRootDensity
import ErdosProblems.Erdos587.CompleteRootDensity
import ErdosProblems.Erdos587.SmoothedCounts
import ErdosProblems.Erdos587.FullPeriodDensity
import ErdosProblems.Erdos587.CenteredCyclic
import ErdosProblems.Erdos587.CyclicPrefix
import ErdosProblems.Erdos587.CyclicBlocks
import ErdosProblems.Erdos587.WideRectangle
import ErdosProblems.Erdos587.WideScales
import ErdosProblems.Erdos587.ProgressionGeometry
import ErdosProblems.Erdos587.WideTerminal
import ErdosProblems.Erdos587.FrequencyWeights
import ErdosProblems.Erdos587.CriticalWeighted
import ErdosProblems.Erdos587.FourierDecay
import ErdosProblems.Erdos587.CriticalCutoffs
import ErdosProblems.Erdos587.LatticeBounds
import ErdosProblems.Erdos587.UniformNearby
import ErdosProblems.Erdos587.PrefixTail
import ErdosProblems.Erdos587.CriticalFullSeries
import ErdosProblems.Erdos587.SignedNearby
import ErdosProblems.Erdos587.CriticalSignedSeries
import ErdosProblems.Erdos587.CriticalZero
import ErdosProblems.Erdos587.CriticalError
import ErdosProblems.Erdos587.Periodization
import ErdosProblems.Erdos587.NearbyCounting
import ErdosProblems.Erdos587.IntegralPeriodization
import ErdosProblems.Erdos587.AlternativeMain
import ErdosProblems.Erdos587.CountComparison
import ErdosProblems.Erdos587.CountWitness
import ErdosProblems.Erdos587.PeriodizedPositivity
import ErdosProblems.Erdos587.AlternativeRoots
import ErdosProblems.Erdos587.AlternativeDensity
import ErdosProblems.Erdos587.FiberIntegral
import ErdosProblems.Erdos587.AlternativeLower
import ErdosProblems.Erdos587.CriticalMain
import ErdosProblems.Erdos587.CompactWeights
import ErdosProblems.Erdos587.RootWeightGeometry
import ErdosProblems.Erdos587.FiniteComparison
import ErdosProblems.Erdos587.CriticalSquare
import ErdosProblems.Erdos587.PrimitiveParameters
import ErdosProblems.Erdos587.CriticalTerminal
import ErdosProblems.Erdos587.LargePrimitive
import ErdosProblems.Erdos587.FiberReduction
import ErdosProblems.Erdos587.SqrtPhase
import ErdosProblems.Erdos587.ShortDifferencing
import ErdosProblems.Erdos587.IntervalDifferencing
import ErdosProblems.Erdos587.FirstDerivativeSum
import ErdosProblems.Erdos587.InversePhaseGeometry
import ErdosProblems.Erdos587.FirstDerivativeTest
import ErdosProblems.Erdos587.MonotoneBands
import ErdosProblems.Erdos587.SecondDerivativePartition
import ErdosProblems.Erdos587.SecondDerivativeTest
import ErdosProblems.Erdos587.FiniteDifferences
import ErdosProblems.Erdos587.DerivativeDifferences
import ErdosProblems.Erdos587.ThirdDifferenceTest
import ErdosProblems.Erdos587.ThirdDifferenceScales
import ErdosProblems.Erdos587.OneSixthPair
import ErdosProblems.Erdos587.HarmonicOneSixth
import ErdosProblems.Erdos587.SqrtPhaseBounds
import ErdosProblems.Erdos587.FractionalFourier
import ErdosProblems.Erdos587.LocatorFourier
import ErdosProblems.Erdos587.LocatorWeight
import ErdosProblems.Erdos587.SqrtPhaseSum
import ErdosProblems.Erdos587.LocatorBudget
import ErdosProblems.Erdos587.SmoothLocator
import ErdosProblems.Erdos587.OneSixthLocator
import ErdosProblems.Erdos587.SqrtLocator
import ErdosProblems.Erdos587.UnitFiberGeometry
import ErdosProblems.Erdos587.UnitFiberBudget
import ErdosProblems.Erdos587.SquareGapLift
import ErdosProblems.Erdos587.UnitFiberTerminal
import ErdosProblems.Erdos587.SmallFiberScales
import ErdosProblems.Erdos587.ThickFiber
import ErdosProblems.Erdos587.SmallPrimitive
import ErdosProblems.Erdos587.PrimitiveTerminal
import ErdosProblems.Erdos587.CongruenceBasis
import ErdosProblems.Erdos587.LatticeQuadratic
import ErdosProblems.Erdos587.ReducedCongruenceBasis
import ErdosProblems.Erdos587.ReducedBasisGeometry
import ErdosProblems.Erdos587.CongruenceBasisImage
import ErdosProblems.Erdos587.LatticeCenter
import ErdosProblems.Erdos587.LatticeBox
import ErdosProblems.Erdos587.LatticeProperness
import ErdosProblems.Erdos587.LatticeDualBound
import ErdosProblems.Erdos587.LatticeBoxSize
import ErdosProblems.Erdos587.LatticeBoxProjection
import ErdosProblems.Erdos587.LatticeNaturalRectangle
import ErdosProblems.Erdos587.ReducedLatticeBox
import ErdosProblems.Erdos587.ReducedLatticeBoxBounds
import ErdosProblems.Erdos587.LatticeAxisWidth
import ErdosProblems.Erdos587.ReducedLatticeBoxWidth
import ErdosProblems.Erdos587.CommonFactorGeometry
import ErdosProblems.Erdos587.NonprimitiveRoots
import ErdosProblems.Erdos587.RootResidueInterval
import ErdosProblems.Erdos587.NonprimitiveRootWindow
import ErdosProblems.Erdos587.NonprimitiveLongSide
import ErdosProblems.Erdos587.CommonFactorPowerScales
import ErdosProblems.Erdos587.CommonFactorLogScales
import ErdosProblems.Erdos587.CommonFactorParameters
import ErdosProblems.Erdos587.CommonFactorTerminal
import ErdosProblems.Erdos587.HomogeneousTerminal
import ErdosProblems.Erdos587.TranslationGrowth
import ErdosProblems.Erdos587.GreedySubsetSums
import ErdosProblems.Erdos587.GreedyGrowthBounds
import ErdosProblems.Erdos587.CosetPacking
import ErdosProblems.Erdos587.LatticeBoxPacking
import ErdosProblems.Erdos587.LatticeIndexBound
import ErdosProblems.Erdos587.BoundedRemoval
import ErdosProblems.Erdos587.SubgroupStability
import ErdosProblems.Erdos587.BoxSubgroupStability
import ErdosProblems.Erdos587.MultiplicativeRemoval
import ErdosProblems.Erdos587.VolumeStability
import ErdosProblems.Erdos587.BoundingBoxVolume
import ErdosProblems.Erdos587.GAPCoordinates
import ErdosProblems.Erdos587.GAPContraction
import ErdosProblems.Erdos587.DyadicSumsets
import ErdosProblems.Erdos587.GAPTrimVolumes
import ErdosProblems.Erdos587.HighFoldModels
import ErdosProblems.Erdos587.GAPDilationCover
import ErdosProblems.Erdos587.DenseHighFold
import ErdosProblems.Erdos587.HighFoldStability
import ErdosProblems.Erdos587.StableHighFoldModels
import ErdosProblems.Erdos587.GAPImageSums
import ErdosProblems.Erdos587.StableCoordinateModel
import ErdosProblems.Erdos587.FiniteQuotientCoverage
import ErdosProblems.Erdos587.CoordinateResidueCorrection
import ErdosProblems.Erdos587.ReserveHomogeneity
import ErdosProblems.Erdos587.GreedyDensity
import ErdosProblems.Erdos587.GreedyDenseFiber
import ErdosProblems.Erdos587.DenseFiberBlocks
import ErdosProblems.Erdos587.DenseSubsetProgression
import ErdosProblems.Erdos587.HomogeneousSubsetProgression
import ErdosProblems.Erdos587.PolynomialDenseRows
import ErdosProblems.Erdos587.PolynomialDenseBoxes
import ErdosProblems.Erdos587.PolynomialDenseProper
import ErdosProblems.Erdos587.PolynomialDenseStandard
import ErdosProblems.Erdos587.PolynomialSubsetProgression
import ErdosProblems.Erdos587.LowerBoundMax
import ErdosProblems.Erdos587.GAPCoverPeriods
import ErdosProblems.Erdos587.DivisibilityReserve
import ErdosProblems.Erdos587.UniformHighFold
import ErdosProblems.Erdos587.PrescribedRank
import ErdosProblems.Erdos587.MultiscaleSubsetProgression
import ErdosProblems.Erdos587.SubgroupStableMultiscale
import ErdosProblems.Erdos587.AsymptoticBounds

/-!
# Erdős Problem 587: unconditional bounds for square-free subset sums

For the maximum size `MaxNotSqSum N` of a subset of `[1,N]` with no
nonempty square subset sum, this development proves the results of
`tex/587.tex`:

* `Erdos587.lower_bound`: `N^(1/3)/4 ≤ MaxNotSqSum N` for `N ≥ 64`.
* `Erdos587.unconditional_nguyen_vu`: an eventual upper bound
  `MaxNotSqSum N ≤ K * N^(1/3) * (log N)^O`, for absolute positive constants.
* `Erdos587.upper_bound`: the same bound with an explicit existential
  natural threshold rather than filter notation.
* `Erdos587.subpolynomial_upper_bound`: the weaker exponential-logarithmic
  upper bound from the comparison section.
* `Erdos587.erdos_587`: for every positive `ε`, eventually
  `N^(1/3-ε) ≤ MaxNotSqSum N ≤ N^(1/3+ε)`.

The proof does not assume Nguyen--Vu's false composite-modulus Weyl lemma
or the faulty projection-index inference in the cited CFP proof.
`SourceAudit.lean` and `CFPSourceAudit.lean` record the corresponding checked
counterexamples; see `SOURCE_AUDIT.md` for their precise scope.

The analytic route uses the corrected reciprocal quadratic mean, exact
Gauss--Fresnel reciprocity, and the homogeneous rank-two square-location
result in `HomogeneousTerminal.lean`. The structural route proves uniform
high-fold doubling, prescribed-scale models, and a rank bound by counting.
`GreedyMultiscale.lean` supplies constant-cost dense subset sums, and
`FiniteStructure.lean` constructs a proper homogeneous rank-one or rank-two
progression with retained side lengths, cardinality, and fixed base/span ratio.
`StructuralTerminal.lean` connects that progression to the analytic result.
`DyadicSquareForcing.lean`, `DyadicSurplus.lean`, and
`UnconditionalUpperBound.lean` select all numerical parameters and finish
without structural or analytic hypotheses.

No `sorry`, added axiom, or computational-limit override occurs in these
Erdos587 sources. The pinned Hasse dependency's Mathlib API compatibility
patch is documented in `DependencyPatches/README.md`.
-/

open Filter

namespace Erdos587

/-- The corrected Formal Conjectures target for Erdős Problem 587. -/
def NguyenVuBound : Prop :=
  ∃ᵉ (O > 0) (O' > 0), ∀ᶠ N : ℕ in atTop,
    (MaxNotSqSum N : ℝ) ≤
      O' * Real.nthRoot 3 N * (N : ℝ).log ^ O

/-- The target is equivalent to the uniform bound for every admissible
finite set; this is the interface used by the Nguyen--Vu development. -/
theorem nguyenVuBound_iff_eventual_uniform_card_bound :
    NguyenVuBound ↔
      (∃ᵉ (O > 0) (O' > 0), ∀ᶠ N : ℕ in atTop,
        ∀ A ⊆ Finset.Icc 1 N, SquareSubsetSumFree A →
          (A.card : ℝ) ≤
            O' * Real.nthRoot 3 N * (N : ℝ).log ^ O) := by
  exact nguyen_vu_iff_eventual_uniform_card_bound

/-- The unconditional upper bound, in the exact target proposition. -/
theorem nguyenVuBound : NguyenVuBound := unconditional_nguyen_vu

/-- A cube-root lower bound for every $N \ge 64$. -/
theorem erdos_587.variants.lower_bound (N : ℕ) (hN : 64 ≤ N) :
    (N : ℝ) ^ (1 / 3 : ℝ) / 4 ≤ (MaxNotSqSum N : ℝ) := by
  exact cube_root_div_four_le_maxNotSqSum N hN

/-- The corrected Formal Conjectures Nguyen--Vu variant. -/
theorem erdos_587.variants.nguyen_vu : ∃ᵉ (O > 0) (O' > 0),
    ∀ᶠ N in Filter.atTop,
      (MaxNotSqSum N : ℝ) ≤
        O' * (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ).log ^ O := by
  simpa only [NguyenVuBound, nthRoot_three_natCast, one_div] using nguyenVuBound

/-- Growth $N^{1/3+o(1)}$, expressed by eventual bounds for every positive $\varepsilon$. -/
theorem erdos_587 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ (1 / 3 - ε) ≤ (MaxNotSqSum N : ℝ) ∧
        (MaxNotSqSum N : ℝ) ≤ (N : ℝ) ^ (1 / 3 + ε) := by
  exact eventually_power_bounds ε hε

end Erdos587
