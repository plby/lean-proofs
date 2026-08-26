/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos67b.MRRealPrefixCompleteStability
import ErdosProblems.Erdos67b.MRScheduledSmallEnergy
import ErdosProblems.Erdos67b.MRComplexMeanSquareComplete
import ErdosProblems.Erdos67b.MRFixedTypicalShortIntervals
import ErdosProblems.Erdos67b.MRTCharacterResidues
import ErdosProblems.Erdos67b.MRTMajorArcTypical
import ErdosProblems.Erdos67b.MRTMinorArcFiniteFamily
import ErdosProblems.Erdos67b.MRTAllFrequencies
import ErdosProblems.Erdos67b.MRTComplete
import ErdosProblems.Erdos67b.ElliottComplete
import ErdosProblems.Erdos67b.StochasticComplete
import ErdosProblems.Erdos67b.FourierLaw
import ErdosProblems.Erdos67b.PrimeGraphFourierUpper
import ErdosProblems.Erdos67b.MRCrossBlockEnergy
import ErdosProblems.Erdos67b.MRSourceProductMoment
import ErdosProblems.Erdos67b.MRFirstSmallBlockClass
import ErdosProblems.Erdos67b.MRScheduledFrequencyClass
import ErdosProblems.Erdos67b.MRFiniteTypicalRamare
import ErdosProblems.Erdos67b.MRCombinedBoundary
import ErdosProblems.Erdos67b.MRPrimeSquareEnergy
import ErdosProblems.Erdos67b.MRClassSummation
import ErdosProblems.Erdos67b.MRExceptionalParameters
import ErdosProblems.Erdos67b.MRSparseDuality
import ErdosProblems.Erdos67b.MRSparseCofactorSamples
import ErdosProblems.Erdos67b.MRExceptionalSmallPrimeEnergy
import ErdosProblems.Erdos67b.MRExceptionalScale
import ErdosProblems.Erdos67b.MRLargePrimeSamples
import ErdosProblems.Erdos67b.MRScheduledMaskSum
import ErdosProblems.Erdos67b.MRTypicalCofactorEuler
import ErdosProblems.Erdos67b.MRShiftedMaskSum
import ErdosProblems.Erdos67b.MRTypicalCofactorVertical
import ErdosProblems.Erdos67b.MRTypicalCofactorProjectionMajorant
import ErdosProblems.Erdos67b.MRTypicalCofactorSecondaries
import ErdosProblems.Erdos67b.MRTypicalCofactorPrefixBound
import ErdosProblems.Erdos67b.MRCofactorScaledDistance
import ErdosProblems.Erdos67b.MRTypicalCofactorUniformPrefix
import ErdosProblems.Erdos67b.MRCofactorAverageEnvelopeScalar
import ErdosProblems.Erdos67b.MRCofactorRowHeight
import ErdosProblems.Erdos67b.MRTypicalCofactorSmallMean
import ErdosProblems.Erdos67b.MRCofactorDyadicSmallMean
import ErdosProblems.Erdos67b.MRCofactorCanonicalRectangle
import ErdosProblems.Erdos67b.MRCofactorAuxiliaryNarrow
import ErdosProblems.Erdos67b.MRAuxiliarySourceRamare
import ErdosProblems.Erdos67b.MRGSTypicalRenormalizationScalar
import ErdosProblems.Erdos67b.MRGSTypicalSourceRenormalization
import ErdosProblems.Erdos67b.MRGSCentralEnergy
import ErdosProblems.Erdos67b.MRCofactorSelectedAmbient
import ErdosProblems.Erdos67b.MRSelectedPrimeIntervalMass
import ErdosProblems.Erdos67b.MRCofactorSelectedSmallMean
import ErdosProblems.Erdos67b.MRPrimeSelbergIntervalMass
import ErdosProblems.Erdos67b.MRSelectedPrimeShiftedCost
import ErdosProblems.Erdos67b.MRSmoothPrimeSelbergKernel
import ErdosProblems.Erdos67b.MRSmoothPrimeSelbergOscillation
import ErdosProblems.Erdos67b.MRSparsePrimeNormalizedEnergy

/-!
# Erdős Problem 67: the unconditional discrepancy theorem

The arbitrary sign sequence is converted to one probability law on completely
multiplicative circle-valued functions by the proved finite Fourier-box and
compactness construction. `StochasticComplete` rules out a uniform second-moment
bound for that law, using the proved unit-circle Elliott theorem and the
same-sample Euler/BCC contradiction.

The analytic chain includes complete complex short-interval and modulated MRT
proofs, the finite entropy/prime-graph argument, uniform twist separation,
Euler residue estimates, and primitive-character orthogonality. No analytic
paper theorem is assumed. The original sequence need not be multiplicative.

The detailed proof and Leanization map are in `tex/67.tex`; exact verification
commands and results are in `Erdos67b/PROGRESS.md`.
-/

open scoped BigOperators

namespace Erdos67b

/-- The Erdős discrepancy theorem for every arbitrary real sign sequence. -/
theorem erdos_67 (f : ℕ → ℝ) (hf : ∀ n, f n = -1 ∨ f n = 1)
    (C : ℝ) (hC : 0 < C) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ C < |∑ k ∈ Finset.Icc 1 m, f (k * d)| := by
  exact sign_discrepancy_of_stochastic stochasticDiscrepancyStatement f hf C hC

/-- The same theorem with a literal `{-1,+1}`-valued function. -/
theorem erdos_67_subtype (f : ℕ → {x : ℝ // x = -1 ∨ x = 1})
    (C : ℝ) (hC : 0 < C) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ C < |∑ k ∈ Finset.Icc 1 m, (f (k * d)).val| := by
  exact erdos_67 (fun n ↦ (f n).val) (fun n ↦ (f n).property) C hC

end Erdos67b
