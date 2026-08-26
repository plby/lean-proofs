import ErdosProblems.Erdos520.Basic
import ErdosProblems.Erdos520.CaichReduction
import ErdosProblems.Erdos520.CaichAlignedFinalAssembly
import ErdosProblems.Erdos520.CaichAlignedResidualL12
import ErdosProblems.Erdos520.ConcreteThinBlock
import ErdosProblems.Erdos520.GranularFinal
import ErdosProblems.Erdos520.LTWMeshGap
import ErdosProblems.Erdos520.Model
import ErdosProblems.Erdos520.ThinBlock
import ErdosProblems.Erdos520.ThinBlockTail

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory

namespace Erdos
namespace Problem520

/-- The formal zero-LIL statement for the squarefree Rademacher model. -/
def Erdos520Disproof : Prop :=
  ZeroLIL μ partialSum

/-- The corresponding explicit negation of a positive limiting LIL constant. -/
def Erdos520NoPositiveConstant : Prop :=
  NoPositiveLILConstant μ partialSum

/-- Historical thin-block interface for the lemmas retained from Caich's
current paper.

The field `criticalUpperBound_of_thinBlock` packages the published
decomposition, smoothing, small-energy estimate, stopped martingale
concentration, smooth-number bound, and interpolation.  Its input is exactly
the new thin-block moment estimate (16).  Instantiating this structure is a
formalization task: the paper is not imported as an axiom.
-/
structure CaichCurrentInputs where
  thinBlockData : ThinBlockData Omega
  criticalUpperBound_of_thinBlock :
    ThinPrimeBlockMomentBound μ thinBlockData →
      CriticalUpperBound μ partialSum

/-- The thin-block moment ingredient, separated from Caich's other inputs. -/
def CaichRepairCertificate (hCaich : CaichCurrentInputs) : Prop :=
  ThinPrimeBlockMomentBound μ hCaich.thinBlockData

/-- Conditional formal endpoint of the historical thin-block route. -/
theorem erdos520Disproof_of_caichCurrentInputs
    (hCaich : CaichCurrentInputs)
    (hRepair : CaichRepairCertificate hCaich) :
    Erdos520Disproof :=
  zeroLIL_of_criticalUpperBound
    (hCaich.criticalUpperBound_of_thinBlock hRepair)

/-- The zero-LIL endpoint rules out every positive limiting constant. -/
theorem erdos520NoPositiveConstant_of_disproof
    (h : Erdos520Disproof) :
    Erdos520NoPositiveConstant :=
  noPositiveLILConstant_of_zeroLIL h

/-- Direct conditional statement of the negative answer to Erdős #520. -/
theorem erdos520NoPositiveConstant_of_caichCurrentInputs
    (hCaich : CaichCurrentInputs)
    (hRepair : CaichRepairCertificate hCaich) :
    Erdos520NoPositiveConstant :=
  erdos520NoPositiveConstant_of_disproof
    (erdos520Disproof_of_caichCurrentInputs hCaich hRepair)

/-- Granular endpoint using the now-formal paper-independent downstream
reduction from localized `2⁻ell` tails. -/
theorem erdos520Disproof_of_caichPostTailInputs
    (hCaich : CaichPostTailInputs μ partialSum) :
    Erdos520Disproof :=
  zeroLIL_of_criticalUpperBound
    (criticalUpperBound_of_caichPostTailInputs hCaich)

/-- Negative answer to Erdős #520 from the granular Caich inputs. -/
theorem erdos520NoPositiveConstant_of_caichPostTailInputs
    (hCaich : CaichPostTailInputs μ partialSum) :
    Erdos520NoPositiveConstant :=
  erdos520NoPositiveConstant_of_disproof
    (erdos520Disproof_of_caichPostTailInputs hCaich)

/-- The remaining published material, phrased after the new moment estimate
but before its conditional-Markov specialization.

For each exponent `eta`, `thinBlockData eta` is the concrete Caich schedule.
The field `postTailInputs_of_localizedTail` packages only the retained
published decomposition/smoothing/concentration inputs: it consumes the
localized `2⁻ell` estimate instead of assuming that estimate itself. -/
structure CaichPublishedTailCompletion where
  thinBlockData : ℝ → ThinBlockData Omega
  I_stronglyMeasurable : ∀ η ell j,
    StronglyMeasurable[(thinBlockData η).filtration ell (j - 1)]
      ((thinBlockData η).I ell (j - 1))
  I_nonneg : ∀ η ell j omega, 0 ≤ (thinBlockData η).I ell j omega
  postTailInputs_of_localizedTail :
    (∀ η : ℝ, 0 < η →
      ∃ C0 : ℝ, 0 < C0 ∧
        ∀ ell j : ℕ, 1 ≤ j → j ≤ (thinBlockData η).J ell →
          ∀ A B : ℝ, 0 < A → 0 < B → 2 * C0 ≤ B →
            μ.real
                (localizedThinBlockBad (thinBlockData η) ell j A B) ≤
              (1 / 2 : ℝ) ^ ell) →
      CaichPostTailInputs μ partialSum

/-- Fully wired reduction from equation (16), through conditional Markov,
the honest union bound and Borel--Cantelli, to the negative answer to #520.
Only the published-tail completion and the concrete moment estimates remain
as arguments. -/
theorem erdos520Disproof_of_publishedCompletion_and_moment
    (hCaich : CaichPublishedTailCompletion)
    (hMoment : ∀ η : ℝ, 0 < η →
      ThinPrimeBlockMomentBound μ (hCaich.thinBlockData η)) :
    Erdos520Disproof := by
  apply erdos520Disproof_of_caichPostTailInputs
  apply hCaich.postTailInputs_of_localizedTail
  intro η hη
  exact exists_localizedThinBlockTailConstant_allScales
    (hCaich.thinBlockData η) (hCaich.I_stronglyMeasurable η)
      (hCaich.I_nonneg η) (hMoment η hη)

/-- Direct no-positive-constant endpoint for the fully wired reduction. -/
theorem erdos520NoPositiveConstant_of_publishedCompletion_and_moment
    (hCaich : CaichPublishedTailCompletion)
    (hMoment : ∀ η : ℝ, 0 < η →
      ThinPrimeBlockMomentBound μ (hCaich.thinBlockData η)) :
    Erdos520NoPositiveConstant :=
  erdos520NoPositiveConstant_of_disproof
    (erdos520Disproof_of_publishedCompletion_and_moment hCaich hMoment)

/-- Fully concrete use of the Doob--Bonami--Minkowski repair.

For each positive `eta`, the only remaining schedule-facing obligation is to
exhibit a `ConcreteThinBlockSchedule` whose two analytic fields are the
Parseval/normalized-energy comparison and the reciprocal-prime block bound.
The concrete equation-(16) proof then supplies the moment hypothesis required
by `CaichPublishedTailCompletion`. -/
theorem erdos520Disproof_of_publishedCompletion_and_concreteSchedules
    (hCaich : CaichPublishedTailCompletion)
    (hSchedules : ∀ eta : ℝ, 0 < eta →
      ∃ s : ConcreteThinBlockSchedule,
        s.toThinBlockData = hCaich.thinBlockData eta) :
    Erdos520Disproof := by
  apply erdos520Disproof_of_publishedCompletion_and_moment hCaich
  intro eta heta
  obtain ⟨s, hs⟩ := hSchedules eta heta
  exact hs ▸ s.thinPrimeBlockMomentBound

/-- Direct negative answer to Erdős #520 from concrete thin-block schedules
and the retained published-tail completion. -/
theorem erdos520NoPositiveConstant_of_publishedCompletion_and_concreteSchedules
    (hCaich : CaichPublishedTailCompletion)
    (hSchedules : ∀ eta : ℝ, 0 < eta →
      ∃ s : ConcreteThinBlockSchedule,
        s.toThinBlockData = hCaich.thinBlockData eta) :
    Erdos520NoPositiveConstant :=
  erdos520NoPositiveConstant_of_disproof
    (erdos520Disproof_of_publishedCompletion_and_concreteSchedules
      hCaich hSchedules)

/-! ## Active granular endpoint -/

/-- Active zero-LIL endpoint with no catch-all published-completion
structure.  Its inputs are the exact Harper and LTW specializations and the
literal aligned smoothing remainder. -/
theorem erdos520Disproof_of_harper_ltw_concreteAuxiliary
    (hHarper : HarperRademacherInitialMomentStatement)
    (hLTW : LauTenenbaumWuRademacherInterpolation)
    (hAux : AlignedConcreteSmoothingAuxiliaryStatement hHarper) :
    Erdos520Disproof :=
  zeroLIL_of_harper_ltw_concreteAuxiliary hHarper hLTW hAux

/-- Direct no-positive-constant form of the active granular endpoint. -/
theorem erdos520NoPositiveConstant_of_harper_ltw_concreteAuxiliary
    (hHarper : HarperRademacherInitialMomentStatement)
    (hLTW : LauTenenbaumWuRademacherInterpolation)
    (hAux : AlignedConcreteSmoothingAuxiliaryStatement hHarper) :
    Erdos520NoPositiveConstant :=
  noPositiveLILConstant_of_harper_ltw_concreteAuxiliary
    hHarper hLTW hAux

/-- Fully expanded source-component endpoint: the remaining Caich premise
names the deterministic main cleanup and the five separate summable
auxiliary failures. -/
theorem erdos520Disproof_of_harper_ltw_fiveAuxiliaries
    (hHarper : HarperRademacherInitialMomentStatement)
    (hLTW : LauTenenbaumWuRademacherInterpolation)
    (hFive : AlignedCaichFiveAuxiliaryStatement hHarper) :
    Erdos520Disproof :=
  erdos520Disproof_of_harper_ltw_concreteAuxiliary hHarper hLTW
    (alignedConcreteSmoothingAuxiliary_of_fiveComponents hHarper hFive)

/-- Negative answer from the exact five-component Caich input. -/
theorem erdos520NoPositiveConstant_of_harper_ltw_fiveAuxiliaries
    (hHarper : HarperRademacherInitialMomentStatement)
    (hLTW : LauTenenbaumWuRademacherInterpolation)
    (hFive : AlignedCaichFiveAuxiliaryStatement hHarper) :
    Erdos520NoPositiveConstant :=
  erdos520NoPositiveConstant_of_disproof
    (erdos520Disproof_of_harper_ltw_fiveAuxiliaries
      hHarper hLTW hFive)

/-! ## Published-theorem endpoint

All argument-specific obligations are discharged below.  The two premises
are exact propositions recording established unconditional results from the
literature: Harper's Rademacher low-moment theorem and the classical
effective prime number theorem.  Lau--Tenenbaum--Wu interpolation and every
Caich-specific residual estimate are proved internally in this development.
-/

/-- The repaired `1/4 + η` upper bound from the two exact published inputs.
No Caich decomposition, smoothing, concentration, interpolation, or
residual-tail hypothesis remains. -/
theorem criticalUpperBound_of_harper_and_effectivePNT
    (hHarper : HarperRademacherInitialMomentStatement)
    (hPNT : EffectivePrimeCountingStatement) :
    CriticalUpperBound μ partialSum := by
  apply criticalUpperBound_of_ltwRademacherTestPoints
  · intro η hη
    obtain ⟨K, hK, hcriticalGap⟩ :=
      exists_alignedDegree_for_criticalGap hη
    let q := selectedCaichAuxiliaryMomentDegree K ltwRootExpDenominator
    have hq : 1 ≤ q := by
      simpa only [q] using!
        one_le_selectedCaichAuxiliaryMomentDegree K ltwRootExpDenominator
    have hWgap : 12 * (2 ^ K) *
        (2 * ltwRootExpDenominator + 2) ≤ q := by
      simpa only [q] using!
        caichWGap_selectedCaichAuxiliaryMomentDegree
          K ltwRootExpDenominator
    have hL12 :=
      summable_measureReal_selectedAlignedHarperL12_failure
        hK hHarper q ltwRootExpDenominator
    have hL2 :=
      summable_measureReal_selectedAlignedHarperL2_failure_of_smoothingExponent
        hK hHarper q ltwRootExpDenominator (by
          simpa only [q] using!
            caichL2Gap_selectedCaichAuxiliaryMomentDegree
              K ltwRootExpDenominator)
    have hpoints :=
      aeTestPointBound_partialSum_of_selectedAlignedResiduals
        hPNT hK ltwRootExpDenominator_pos hq hWgap hη hcriticalGap
          hHarper hL12 hL2
    simpa only [ltwRademacherTestPoint] using! hpoints
  · exact LauTenenbaumWuRademacherInterpolation_unconditional

/-- The repaired `1/4 + η` upper bound from Harper's exact moment input.
The prime short-window estimate is discharged internally by the verified
Brun--Titchmarsh sieve. -/
theorem criticalUpperBound_of_harper
    (hHarper : HarperRademacherInitialMomentStatement) :
    CriticalUpperBound μ partialSum := by
  apply criticalUpperBound_of_ltwRademacherTestPoints
  · intro η hη
    obtain ⟨K, hK, hcriticalGap⟩ :=
      exists_alignedDegree_for_criticalGap hη
    let q := selectedCaichAuxiliaryMomentDegree K ltwRootExpDenominator
    have hq : 1 ≤ q := by
      simpa only [q] using!
        one_le_selectedCaichAuxiliaryMomentDegree K ltwRootExpDenominator
    have hWgap : 12 * (2 ^ K) *
        (2 * ltwRootExpDenominator + 2) ≤ q := by
      simpa only [q] using!
        caichWGap_selectedCaichAuxiliaryMomentDegree
          K ltwRootExpDenominator
    have hL12 :=
      summable_measureReal_selectedAlignedHarperL12_failure
        hK hHarper q ltwRootExpDenominator
    have hL2 :=
      summable_measureReal_selectedAlignedHarperL2_failure_of_smoothingExponent
        hK hHarper q ltwRootExpDenominator (by
          simpa only [q] using!
            caichL2Gap_selectedCaichAuxiliaryMomentDegree
              K ltwRootExpDenominator)
    have hpoints :=
      aeTestPointBound_partialSum_of_selectedAlignedResiduals_unconditional
        hK ltwRootExpDenominator_pos hq hWgap hη hcriticalGap
          hHarper hL12 hL2
    simpa only [ltwRademacherTestPoint] using! hpoints
  · exact LauTenenbaumWuRademacherInterpolation_unconditional

/-- Complete negative answer to Erdős #520 from the two established
published analytic theorems. -/
theorem erdos520Disproof_of_harper_and_effectivePNT
    (hHarper : HarperRademacherInitialMomentStatement)
    (hPNT : EffectivePrimeCountingStatement) :
    Erdos520Disproof :=
  zeroLIL_of_criticalUpperBound
    (criticalUpperBound_of_harper_and_effectivePNT hHarper hPNT)

/-- Direct statement that no positive limiting LIL constant can occur. -/
theorem erdos520NoPositiveConstant_of_harper_and_effectivePNT
    (hHarper : HarperRademacherInitialMomentStatement)
    (hPNT : EffectivePrimeCountingStatement) :
    Erdos520NoPositiveConstant :=
  erdos520NoPositiveConstant_of_disproof
    (erdos520Disproof_of_harper_and_effectivePNT hHarper hPNT)

/-- Negative answer to Erdős #520 with the prime input proved internally.
Only Harper's Rademacher low-moment statement remains as an explicit
published-theorem premise. -/
theorem erdos520Disproof_of_harper
    (hHarper : HarperRademacherInitialMomentStatement) :
    Erdos520Disproof :=
  zeroLIL_of_criticalUpperBound (criticalUpperBound_of_harper hHarper)

/-- Direct statement that no positive limiting LIL constant can occur,
assuming only Harper's Rademacher low-moment statement. -/
theorem erdos520NoPositiveConstant_of_harper
    (hHarper : HarperRademacherInitialMomentStatement) :
    Erdos520NoPositiveConstant :=
  erdos520NoPositiveConstant_of_disproof
    (erdos520Disproof_of_harper hHarper)

end Problem520
end Erdos
