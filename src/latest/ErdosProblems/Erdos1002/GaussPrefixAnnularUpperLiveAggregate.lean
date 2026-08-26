import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperDigitTransfer
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFreezingBoundaryAsymptotic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact live-joint change of measure in the upper retained aggregate

The future-digit replacement is first obtained under the original uniform
Lebesgue law, whereas the freezing argument is carried out under Gauss
measure with the exact Lebesgue density.  This file records the finite,
term-by-term change of measure and then exposes the resulting aggregate
limit in the orientation used by the final telescoping argument.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- The uniform live-digit aggregate is exactly the density-weighted Gauss
aggregate at every finite scale. -/
theorem annularContractedUpperRetainedLiveDigitJointSum_eq_weighted
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    annularContractedUpperRetainedLiveDigitJointSum
        ε A eta rho N k hr mode hmode =
      annularContractedUpperRetainedLebesgueWeightedLiveDigitJointSum
        ε A eta rho N k hr mode hmode := by
  unfold annularContractedUpperRetainedLiveDigitJointSum
    annularContractedUpperRetainedLebesgueWeightedLiveDigitJointSum
  apply Finset.sum_congr rfl
  intro p _hp
  exact
    annularContractedUpperRetainedLiveDigitJoint_eq_weighted
      ε A eta rho N k hr mode hmode p

/-- Consequently the original uniform live aggregate and the affine-frozen
weighted aggregate have the same limit. -/
theorem
    tendsto_annularContractedUpperRetainedLiveDigitJointSum_sub_affine_zero
    {eta rho ε A : ℝ} (heta : 0 < eta) (hrho : 0 < rho)
    (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedLiveDigitJointSum
              ε A eta rho N k hr mode hmode -
          annularContractedUpperRetainedLebesgueWeightedAffineDigitJointSum
            ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  simpa only
    [annularContractedUpperRetainedLiveDigitJointSum_eq_weighted] using!
    tendsto_annularContractedUpperRetainedLebesgueWeightedLiveDigitJointSum_sub_affine_zero
      heta hrho hε hεA hgrid k hr htime hsigned mode hmode

end

end Erdos1002
