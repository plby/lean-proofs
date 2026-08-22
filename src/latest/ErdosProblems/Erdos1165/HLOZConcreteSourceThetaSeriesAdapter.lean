/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongComplementSeries
import ErdosProblems.Erdos1165.HLOZConcreteFullBetaProductData
import ErdosProblems.Erdos1165.HLOZNoLazyFiniteSourceRowUpperAssembly
import ErdosProblems.Erdos1165.HLOZRawOrientedSourceThetaPayment

/-!
# Concrete source/Theta series adapter

All source-overflow and candidate-local-complement fields of the corrected
product series record are now concrete.  The only remaining input below is
the separately identified positive-interface physical-balance payment.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZConcreteSourceThetaSeriesAdapter

open HLOZCandidateLocalBroadThetaStrongComplementSeries
open HLOZConcreteFullBetaProductData HLOZNoLazyFiniteSourceRowUpperAssembly
open HLOZRawFullGapProductPromotion HLOZRawOrientedSourceThetaPayment
open HLOZSourceCorrectFullGapClosure LazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The exact residual interface requested from the positive-shell
actual-increment construction. -/
structure ConcretePositiveInterfaceBalanceSeriesData where
  balance : DominoTiling → ℕ → Set WalkPath
  candidateLocal_subset : ∀ t m,
    candidateLocalProductPositiveInterfaceBalanceRemainderEvent
        concreteFullBetaProductData t m ⊆
      balance t m
  firstRaw_subset : ∀ t m a,
    firstRawCandidatePreliminary t m a ∩
        positiveInterfaceBalanceRemainderUnionAtRank
          concreteFullBetaProductData t 1 m ⊆
      balance t m
  secondRaw_subset : ∀ t m a,
    secondRawCandidatePreliminary t m a ∩
        positiveInterfaceBalanceRemainderUnionAtRank
          concreteFullBetaProductData t 2 m ⊆
      balance t m
  thirdRaw_subset : ∀ t m a,
    thirdRawCandidatePreliminary t m a ∩
        positiveInterfaceBalanceRemainderUnionAtRank
          concreteFullBetaProductData t 3 m ⊆
      balance t m
  series : ∀ t, ∑' m, simpleRandomWalk (balance t m) ≠ ∞

/-- Fill every source/Theta/complement field of the final corrected-product
record from the concrete construction. -/
def correctedProductSourceThetaSeriesData_of_balance
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (balance : ConcretePositiveInterfaceBalanceSeriesData) :
    CorrectedProductSourceThetaSeriesData concreteFullBetaProductData where
  balance := balance.balance
  sourceOne := fun t m ↦ rawOrientedSourceThetaTotalPaymentAtRank
    concreteFullBetaProductData t 1 m
  sourceTwo := fun t m ↦ rawOrientedSourceThetaTotalPaymentAtRank
    concreteFullBetaProductData t 2 m
  sourceThree := fun t m ↦ rawOrientedSourceThetaTotalPaymentAtRank
    concreteFullBetaProductData t 3 m
  candidateLocalBalance_subset := balance.candidateLocal_subset
  candidateLocalOne_subset :=
    candidateLocalSourceOne_subset_rawOrientedSourceThetaTotalPayment
      concreteFullBetaProductData
  candidateLocalTwo_subset :=
    candidateLocalSourceTwo_subset_rawOrientedSourceThetaTotalPayment
      concreteFullBetaProductData
  candidateLocalThree_subset :=
    candidateLocalSourceThree_subset_rawOrientedSourceThetaTotalPayment
      concreteFullBetaProductData
  firstRawBalance_subset := balance.firstRaw_subset
  secondRawBalance_subset := balance.secondRaw_subset
  thirdRawBalance_subset := balance.thirdRaw_subset
  firstRawSource_subset :=
    firstRawSource_subset_rawOrientedSourceThetaTotalPayment
      concreteFullBetaProductData
  secondRawSource_subset :=
    secondRawSource_subset_rawOrientedSourceThetaTotalPayment
      concreteFullBetaProductData
  thirdRawSource_subset :=
    thirdRawSource_subset_rawOrientedSourceThetaTotalPayment
      concreteFullBetaProductData
  balance_series := balance.series
  sourceOne_series := fun t ↦
    simpleRandomWalk_rawOrientedSourceThetaTotalPaymentAtRank_series_ne_top
      hProp13 concreteFullBetaProductData t 1 (by omega)
  sourceTwo_series := fun t ↦
    simpleRandomWalk_rawOrientedSourceThetaTotalPaymentAtRank_series_ne_top
      hProp13 concreteFullBetaProductData t 2 (by omega)
  sourceThree_series := fun t ↦
    simpleRandomWalk_rawOrientedSourceThetaTotalPaymentAtRank_series_ne_top
      hProp13 concreteFullBetaProductData t 3 (by omega)
  complement_series := fun t ↦ by
    simpa only [concreteFullBetaProductData, concreteExternalThreshold48]
      using
        simpleRandomWalk_onTimeProductBetaCandidateLocalComplementEvent_half_series_ne_top
          t

end

end Erdos1165.HLOZConcreteSourceThetaSeriesAdapter
