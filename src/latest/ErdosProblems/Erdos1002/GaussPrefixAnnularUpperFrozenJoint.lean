import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperGoodTransfer
import ErdosProblems.Erdos1002.GaussPrefixAnnularMaskedEventBridge
import ErdosProblems.Erdos1002.GaussPrefixLateMeanBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical frozen-joint interface for contracted upper annular tuples

This file fixes the literal functions used after the complete future
exact-to-digit replacement.  In particular:

* the prefix remains restricted to the delayed denominator-good event;
* the future digit block remains attached to every joint integral;
* the prefix is frozen at the delayed depth;
* the residual mixing gap starts exactly at the already-packaged future
  base.

The definitions below are deliberately thin wrappers around the audited
generic prefix-freezing and functional-mixing objects.  Consequently the
density and covariance stages can share one expression rather than
reconstructing propositionally equal variants.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularUpperFrozenJointPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {eta rho ε A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

/-- The uncontracted upper tag underlying a contracted tag. -/
abbrev annularContractedUpperRetainedUpperTag
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    AnnularUpperRetainedTaggedTuple rho N k hr mode hmode :=
  annularContractedUpperRetainedToUpper p

/-- Shallow cutoff used only for the oscillatory prefix estimate. -/
def annularContractedUpperRetainedShallowDepth
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℕ :=
  annularUpperRetainedShallowSplitDepth
    (annularContractedUpperRetainedUpperTag p)

/-- Residual gap available after freezing at the delayed depth. -/
def annularContractedUpperRetainedMixingGap
    (rho : ℝ) (N : ℕ) : ℕ :=
  annularUpperRetainedDelayedMixingGap rho N

/-- Packaged future time tuple. -/
def annularContractedUpperRetainedFutureTime
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    Fin (MixedOccurrenceCount k) → ℕ :=
  annularUpperRetainedFutureTime
    (annularContractedUpperRetainedUpperTag p)

/-- Packaged future one-digit events. -/
def annularContractedUpperRetainedFutureDigitEvent
    (ε A : ℝ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    Fin (MixedOccurrenceCount k) → Set ℝ :=
  annularUpperRetainedFutureDigitEvent ε A
    (annularContractedUpperRetainedUpperTag p)

/-- The literal future digit block kept throughout freezing and mixing. -/
def annularContractedUpperRetainedFutureDigitBlock
    (ε A : ℝ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℝ → ℂ :=
  annularUpperRetainedFutureDigitBlock ε A
    (annularContractedUpperRetainedUpperTag p)

/-- Prefix words admitted by the same delayed denominator-good event used
in the moving-to-prefix transfer. -/
def annularContractedUpperRetainedGoodWords
    (eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    Set (PositiveDigitWord
      (annularContractedUpperRetainedDelayedDepth p)) :=
  gaussDenominatorPrefixGoodWords
    (annularContractedUpperRetainedDelayedDepth p)
    (annularDepthAmbientSize N)
    (upperGoodTransferDenominatorTolerance eta rho)

/-- Delayed depth plus residual gap is literally the future-block base. -/
theorem annularContractedUpperRetained_delayedDepth_add_mixingGap
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedDelayedDepth p +
        annularContractedUpperRetainedMixingGap rho N =
      annularUpperRetainedFutureBase
        (annularContractedUpperRetainedUpperTag p) := by
  simpa only [annularContractedUpperRetainedDelayedDepth,
    annularContractedUpperRetainedMixingGap,
    annularContractedUpperRetainedUpperTag] using!
    annularUpperRetained_delayedSplit_add_mixingGap
      (annularContractedUpperRetainedUpperTag p)

/-- The live delayed-prefix character multiplied by the complete future
digit block, under the original uniform law. -/
def annularContractedUpperRetainedLiveDigitJoint
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∫ x,
    (gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)).indicator
      (fun y ↦
        gaussPrefixMarkedMixedPrefixCharacter N
            (fun i ↦ compactValueMarkedRegion
              (activeAnnularOccurrenceSignedLower k ε A i)
              (activeAnnularOccurrenceSignedUpper k ε A i))
            k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p) y *
          annularContractedUpperRetainedFutureDigitBlock ε A p y) x
    ∂uniform01Measure

/-- The same live joint after the exact Lebesgue-to-Gauss change of
measure.  The non-frozen density is retained literally. -/
def annularContractedUpperRetainedLebesgueWeightedLiveDigitJoint
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∫ x,
    (gaussLebesguePrefixWeight x : ℂ) *
      (gaussDenominatorPrefixGoodEvent
        (annularContractedUpperRetainedDelayedDepth p)
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho)).indicator
        (fun y ↦
          gaussPrefixMarkedMixedPrefixCharacter N
              (fun i ↦ compactValueMarkedRegion
                (activeAnnularOccurrenceSignedLower k ε A i)
                (activeAnnularOccurrenceSignedUpper k ε A i))
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p) y *
            annularContractedUpperRetainedFutureDigitBlock ε A p y) x
    ∂gaussMeasure

/-- Exact change of measure for the complete live prefix--future joint. -/
theorem annularContractedUpperRetainedLiveDigitJoint_eq_weighted
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedLiveDigitJoint
        ε A eta rho N k hr mode hmode p =
      annularContractedUpperRetainedLebesgueWeightedLiveDigitJoint
        ε A eta rho N k hr mode hmode p := by
  unfold annularContractedUpperRetainedLiveDigitJoint
    annularContractedUpperRetainedLebesgueWeightedLiveDigitJoint
  exact integral_uniform01_eq_integral_gaussLebesguePrefixWeight_mul _

/-- Intermediate affine-frozen joint in which the exact
Lebesgue-to-Gauss density is still live.  Prefix freezing compares the
preceding weighted live joint with this expression; density freezing alone
compares this expression with `annularContractedUpperRetainedFrozenDigitJoint`.
Keeping the two operations separate prevents either error from being
hidden in the other. -/
def annularContractedUpperRetainedLebesgueWeightedAffineDigitJoint
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∫ x,
    (gaussLebesguePrefixWeight x : ℂ) *
      gaussPrefixAffineFrozenCompactCharacter
        N
        (activeAnnularOccurrenceSignedLower k ε A)
        (activeAnnularOccurrenceSignedUpper k ε A)
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)
        (annularContractedUpperRetainedGoodWords eta rho N p) x *
      annularContractedUpperRetainedFutureDigitBlock ε A p x
    ∂gaussMeasure

/-- Affine-frozen Gauss joint with frozen Lebesgue density and the same
future digit block. -/
def annularContractedUpperRetainedFrozenDigitJoint
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  gaussLateLebesgueWeightedFrozenJoint
    N
    (activeAnnularOccurrenceSignedLower k ε A)
    (activeAnnularOccurrenceSignedUpper k ε A)
    k
    (unflattenedAnnularFourierMode p.1 (mode p.1))
    (annularContractedUpperRetainedRealization p).1
    (annularContractedUpperRetainedDelayedDepth p)
    (annularContractedUpperRetainedMixingGap rho N)
    (annularContractedUpperRetainedGoodWords eta rho N p)
    (annularContractedUpperRetainedFutureTime p)
    (annularContractedUpperRetainedFutureDigitEvent ε A p)

/-- Prefix mean paired with the preceding frozen joint. -/
def annularContractedUpperRetainedFrozenPrefixMean
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  gaussLateLebesgueWeightedFrozenPrefixMean
    N
    (activeAnnularOccurrenceSignedLower k ε A)
    (activeAnnularOccurrenceSignedUpper k ε A)
    k
    (unflattenedAnnularFourierMode p.1 (mode p.1))
    (annularContractedUpperRetainedRealization p).1
    (annularContractedUpperRetainedDelayedDepth p)
    (annularContractedUpperRetainedGoodWords eta rho N p)

/-- Future mean paired with the preceding frozen joint. -/
def annularContractedUpperRetainedFutureMean
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  gaussLateFutureDigitBlockMean
    (annularContractedUpperRetainedDelayedDepth p +
      annularContractedUpperRetainedMixingGap rho N)
    (annularContractedUpperRetainedFutureTime p)
    (annularContractedUpperRetainedFutureDigitEvent ε A p)

/-- The complete future mean is bounded only after it has been attached
to the same tagged joint used in replacement, freezing, and mixing. -/
theorem norm_annularContractedUpperRetainedFutureMean_le_one
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    ‖annularContractedUpperRetainedFutureMean
        ε A eta rho N k hr mode hmode p‖ ≤ 1 := by
  unfold annularContractedUpperRetainedFutureMean
  exact norm_gaussLateFutureDigitBlockMean_le_one _ _ _

end

end Erdos1002
