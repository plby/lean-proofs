import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperDigitTransfer
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperDensityAggregate
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperLiveAggregate
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFactorizedLimit
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperRestoration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Assembly of the contracted upper-retained limit

This module contains the purely algebraic final telescope for the
upper-retained late case.  All estimates entering the telescope are stated as
limits of literal differences, so no cancellation or change of summation
order is hidden in the assembly.
-/

open Filter
open scoped Topology

namespace Erdos1002

noncomputable section

/-- Once the delayed factorized prefix has been compared with the shallow
factorized prefix, the seven previously established comparison limits and
the terminal shallow cancellation telescope to the literal contracted
moving sum. -/
theorem
    tendsto_annularContractedUpperRetainedMovingSum_zero_of_factorizedBridge
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hfactorizedBridge :
      Tendsto
        (fun N : ℕ ↦
          annularContractedUpperRetainedAffineFactorizedMeanSum
                ε A eta rho N k hr mode hmode -
            annularContractedUpperRetainedShallowFactorizedMeanSum
                ε A eta rho N k hr mode hmode)
        atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedMovingSum
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have hMovingToGood :=
    tendsto_annularContractedUpperRetainedMovingSum_sub_prefixGood_zero
      hε hεA heta hrho hgrid k hr htime hsigned mode hmode
  have hGoodToLive :=
    tendsto_annularContractedUpperRetainedPrefixGoodMixedSum_sub_liveDigitJointSum_zero
      hε hεA heta hrho hgrid k hr htime hsigned mode hmode
  have hLiveToAffine :=
    tendsto_annularContractedUpperRetainedLiveDigitJointSum_sub_affine_zero
      heta hrho hε hεA hgrid k hr htime hsigned mode hmode
  have hDensity :=
    tendsto_annularContractedUpperRetainedLebesgueWeightedAffineDigitJointSum_sub_frozen_zero
      ε A eta rho hgrid k hr htime mode hmode
  have hCovariance :=
    tendsto_annularContractedUpperRetainedFrozenDigitJointSum_sub_factorized_zero
      hrho ε A eta hgrid k hr htime mode hmode
  have hPrefixDensity :=
    tendsto_annularContractedUpperRetainedFactorizedMeanSum_sub_affine_zero
      ε A eta rho hgrid k hr htime mode hmode
  have hShallow :=
    tendsto_annularContractedUpperRetainedShallowFactorizedMeanSum_zero
      hε hεA heta hrho hgrid k hr htime hsigned mode hmode
  have hsum :=
    hMovingToGood.add
      (hGoodToLive.add
        (hLiveToAffine.add
          (hDensity.add
            (hCovariance.add
              (hPrefixDensity.add
                (hfactorizedBridge.add hShallow))))))
  convert! hsum using 1
  · funext N
    ring
  · norm_num

end

end Erdos1002
