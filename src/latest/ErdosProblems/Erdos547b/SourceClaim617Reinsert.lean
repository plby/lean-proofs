/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePathCoreReady
import ErdosProblems.Erdos547b.TwoTierRootPaths

/-! # Complete actual reinsertion of the postponed Claim-6.17 paths -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClaim617Reinsert

open Finset SimpleGraph Erdos547b.TreePartition Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceClaim617PathNumerics Erdos547b.ZhaoClaim617CleanLoss
open Erdos547b.ZhaoClaim617CleanSelection Erdos547b.ZhaoSourcePathCoreReady
open Erdos547b.ZhaoSourceFreedMidpointSystem Erdos547b.ZhaoSourceMidpointNumerics
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceClaim617Switch
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoClaim615SourceSelection

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U} (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (hp : postponedCount α q ≤ (cleanBranches P).card)
variable (O : Output W Q S (branchMass P (sideBranches P 1))) (sw : Switch W Q S O)

include W Q S hT P hp O sw in
theorem exists_copy_of_postponed_switch
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G) : Nonempty (T.Copy G) := by
  obtain ⟨D, f, hfree, hcounts⟩ := exists_readyCore W Q S hT P hp O sw hα hα1 hhost horder hcard hnot
  have hcount : highCount α q ≤ (Finset.univ : Finset (Fin (postponedCount α q))).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using highCount_le_postponed (q := q) hα hα1
  obtain ⟨High, _, hHigh⟩ := Finset.exists_subset_card_eq hcount
  apply (selectedPaths P hp).exists_copy_of_core_twoTier G f High
    (pool W Q S O sw D 0) (pool W Q S O sw D 1) (pools_disjoint W Q S O sw D)
    (hfree 0) (hfree 1)
  · intro i
    rw [hHigh]
    exact (hcounts i).1
  · intro i
    exact (Nat.sub_le _ _).trans (by simpa only [Fintype.card_fin] using (hcounts i).2)
  · intro z hz
    simpa only [hcard, Nat.add_sub_cancel] using high_pool_degree W Q S O sw D hz
  · intro z hz
    simpa only [hcard, Nat.add_sub_cancel, hHigh] using
      low_degree_integer (low_pool_degree W Q S O sw D hz)

end Erdos547b.ZhaoSourceClaim617Reinsert

#print axioms Erdos547b.ZhaoSourceClaim617Reinsert.exists_copy_of_postponed_switch
