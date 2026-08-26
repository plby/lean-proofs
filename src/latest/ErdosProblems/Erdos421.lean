/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Formalization of Erdős Problem 421.
https://www.erdosproblems.com/421

Main declaration: Erdos421.erdos_421, with the original quantifiers and hypotheses.

Construction: Przemek Chojecki.
Selected source: Rob Sneiderman, July 20, 2026, claim #100.
https://github.com/Robby955/erdos-421-audit/blob/318c112c7a70879d98d86d8c3d9a280d77dadb35/paper.pdf

Formal proof: OpenAI Codex, in this repository.

See Erdos421/README.md for the proof outline and verification details.
-/
import ErdosProblems.Erdos421.Rejection
import ErdosProblems.Erdos421.Curves
import ErdosProblems.Erdos421.Counting
import ErdosProblems.Erdos421.LongGaps
import ErdosProblems.Erdos421.ImplicitConvex
import ErdosProblems.Erdos421.LatticeCount
import ErdosProblems.Erdos421.ShortGaps
import ErdosProblems.Erdos421.ShortDensity
import ErdosProblems.Erdos421.Buchstab
import ErdosProblems.Erdos421.MeanSquare
import ErdosProblems.Erdos421.LargeValues
import ErdosProblems.Erdos421.LongOmissionCount
import ErdosProblems.Erdos421.HilbertLargeValues
import ErdosProblems.Erdos421.LogarithmicSums
import ErdosProblems.Erdos421.LogarithmicBounds
import ErdosProblems.Erdos421.WeightedChildren
import ErdosProblems.Erdos421.BoundedOmissionCount
import ErdosProblems.Erdos421.ModerateDensity
import ErdosProblems.Erdos421.HigherHalasz
import ErdosProblems.Erdos421.Vaughan
import ErdosProblems.Erdos421.ConvolutionSums
import ErdosProblems.Erdos421.LogCubicBound
import ErdosProblems.Erdos421.ZetaScaleSaving
import ErdosProblems.Erdos421.StripConstants
import ErdosProblems.Erdos421.ZetaLogZeroFree
import ErdosProblems.Erdos421.ZeroRepresentation
import ErdosProblems.Erdos421.MixedCongruences
import ErdosProblems.Erdos421.PowerSumAffine
import ErdosProblems.Erdos421.VinogradovMoments
import ErdosProblems.Erdos421.PrimePools
import ErdosProblems.Erdos421.PrimeSolutionSelection
import ErdosProblems.Erdos421.MeanValueDefectDecay
import ErdosProblems.Erdos421.TorusBoxes
import ErdosProblems.Erdos421.LogTaylorRemainder
import ErdosProblems.Erdos421.VariationWeights
import ErdosProblems.Erdos421.IntegralOverlap
import ErdosProblems.Erdos421.ShortShiftAverage
import ErdosProblems.Erdos421.PrimeScaleSaving
import ErdosProblems.Erdos421.PrimeFactorShortMean
import ErdosProblems.Erdos421.TwoFactorPowerParameters
import ErdosProblems.Erdos421.VerticalDirichletLargeValues
import ErdosProblems.Erdos421.NormalizedDirichletLargeValues
import ErdosProblems.Erdos421.PrimePolynomialSupport
import ErdosProblems.Erdos421.PrimeCofactorLogSamples
import ErdosProblems.Erdos421.PrimeCofactorMeanSquare
import ErdosProblems.Erdos421.PrimeCofactorUniformMean
import ErdosProblems.Erdos421.PrimeCofactorWeightedMean
import ErdosProblems.Erdos421.PrimeCofactorWindowMean
import ErdosProblems.Erdos421.PrimeCofactorSmoothVariance
import ErdosProblems.Erdos421.PrimeSmoothWindows
import ErdosProblems.Erdos421.ZetaPrimeErrorStrip
import ErdosProblems.Erdos421.PrimeErrorPerron
import ErdosProblems.Erdos421.SmoothedPrimeErrorBound
import ErdosProblems.Erdos421.SmoothedPrimeErrorSaving
import ErdosProblems.Erdos421.ThetaLogSaving
import ErdosProblems.Erdos421.PrimeLogReferenceWindow
import ErdosProblems.Erdos421.DivisorSpectrumMean
import ErdosProblems.Erdos421.FiniteLatticeMean
import ErdosProblems.Erdos421.DivisorWindowUniformBound
import ErdosProblems.Erdos421.DivisorWindowPowerSaving
import ErdosProblems.Erdos421.WeightedBuchstab
import ErdosProblems.Erdos421.SelbergMainTerm
import ErdosProblems.Erdos421.SelbergSupport
import ErdosProblems.Erdos421.UniformResidueSieve
import ErdosProblems.Erdos421.CanonicalLowerSieve
import ErdosProblems.Erdos421.SmoothSieveWindows
import ErdosProblems.Erdos421.RoughEulerHarmonic
import ErdosProblems.Erdos421.SieveWindowErrors
import ErdosProblems.Erdos421.RoughWindowMeanSquare
import ErdosProblems.Erdos421.RoughWindowComparison
import ErdosProblems.Erdos421.LocalLogarithmicWindows
import ErdosProblems.Erdos421.RoughWindowLengthMean
import ErdosProblems.Erdos421.LogarithmicRoughVariance
import ErdosProblems.Erdos421.PrimeCofactorTwoWindows
import ErdosProblems.Erdos421.LogarithmicPrimeMinorant
import ErdosProblems.Erdos421.PartitionedBuchstab
import ErdosProblems.Erdos421.NarrowPrimeBlockMass
import ErdosProblems.Erdos421.TruncatedProductWindows
import ErdosProblems.Erdos421.BoundedPrimeCofactorVariance
import ErdosProblems.Erdos421.LogarithmicCofactorVariance
import ErdosProblems.Erdos421.PrimeReciprocalBands
import ErdosProblems.Erdos421.FullPrimeCofactorVariance
import ErdosProblems.Erdos421.PrimeMinorantTransfer
import ErdosProblems.Erdos421.BuchstabPositiveConstant
import ErdosProblems.Erdos421.RoughBaseAsymptotic
import ErdosProblems.Erdos421.FiniteBuchstabPrimeSaving
import ErdosProblems.Erdos421.RoughCofactorErrors
import ErdosProblems.Erdos421.RoughBoundaryCorrection
import ErdosProblems.Erdos421.RoughCountAsymptotic
import ErdosProblems.Erdos421.LogarithmicRoughAsymptotic
import ErdosProblems.Erdos421.ReferenceRoughWindow
import ErdosProblems.Erdos421.PrimeMinorantReference
import ErdosProblems.Erdos421.CandidateDensity
import Util.Density

namespace Erdos421

/-- The original density-one question, with all its quantifiers preserved. -/
def OriginalStatement : Prop :=
  ∃ d : ℕ → ℕ, StrictMono d ∧ 1 ≤ d 0 ∧ (Set.range d).HasDensity 1 ∧
    {uv : ℕ × ℕ | uv.1 ≤ uv.2}.InjOn
      (fun uv ↦ ∏ i ∈ Finset.Icc uv.1 uv.2, d i)

/-- Chojecki's gap-greedy candidate has density one and distinct products on
all distinct nonempty consecutive index intervals. -/
theorem erdos_421 :
    ∃ d : ℕ → ℕ, StrictMono d ∧ 1 ≤ d 0 ∧ (Set.range d).HasDensity 1 ∧
      {uv : ℕ × ℕ | uv.1 ≤ uv.2}.InjOn
        (fun uv ↦ ∏ i ∈ Finset.Icc uv.1 uv.2, d i) := by
  refine ⟨candidateSequence, candidateSequence_strictMono, ?_, ?_,
    candidateSequence_products_injective⟩
  · exact (by decide : 1 ≤ 2).trans (candidateSequence_two_le 0)
  · rw [range_candidateSequence]
    exact candidate_hasDensity_one

end Erdos421

#print axioms Erdos421.erdos_421
-- 'Erdos421.erdos_421' depends on axioms: [propext, Classical.choice, Quot.sound]
