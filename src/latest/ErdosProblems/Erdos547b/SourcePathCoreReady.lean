/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePathCoreSmallCopy
import ErdosProblems.Erdos547b.SourcePathCoreCopy
import ErdosProblems.Erdos547b.SourceFreedMidpointCapacity

/-! # The actual original-host core has unused pools and live parent neighborhoods -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePathCoreReady

open Finset SimpleGraph Erdos547EC2 Erdos547b.TreePartition Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceClaim617PathNumerics Erdos547b.ZhaoClaim617CleanLoss
open Erdos547b.ZhaoClaim617CleanSelection Erdos547b.ZhaoSourcePathCoreGraph
open Erdos547b.ZhaoSourcePathCoreCopy Erdos547b.ZhaoSourcePathCoreSmallCopy
open Erdos547b.ZhaoSourceFreedMidpointSystem Erdos547b.ZhaoSourceFreedMidpointCapacity
open Erdos547b.ZhaoSourceMidpointNumerics Erdos547b.ZhaoSourceMatchingCopySupport
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceClaim617Switch
open Erdos547b.ZhaoSourceSwitchUnion Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoSourceReconnectedTwoRowCopy
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSection6Dichotomy

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U} (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (hp : postponedCount α q ≤ (cleanBranches P).card)
variable (O : Output W Q S (branchMass P (sideBranches P 1))) (sw : Switch W Q S O)

theorem parentCore_eq_root (i : Fin (postponedCount α q)) :
    (selectedPaths P hp).parentCoreVertex i = pathCorePartitionRoot P hp (selectedRootIndex P hp i) := by
  apply Subtype.ext
  apply Subtype.ext
  exact selectedPaths_parent P hp i

theorem selected_parent_side (i : Fin (postponedCount α q)) :
    componentReservoirSide P (selectedRootIndex P hp i) = 0 := by
  have hparity := selectedPaths_parent_parity P hp i
  rw [selectedPaths_parent] at hparity
  exact if_pos hparity

theorem switched_hostSupport_subset_full :
    hostSupport W Q sw.switched ⊆ hostSupport W Q (fullMatching W Q S O sw) := by
  intro z hz
  rcases Finset.mem_union.mp hz with hroot | hmatch
  · exact Finset.mem_union_left _ hroot
  · obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hmatch
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,
      (fullMatching_support W Q S O sw).symm ▸ Finset.mem_union_left _ hx, hzx⟩)

include hT in
theorem exists_readyCore
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G) :
    ∃ D : Data W Q S O sw, ∃ f : (selectedPaths P hp).core.Copy G,
      (∀ s x, f x ∉ pool W Q S O sw D s) ∧
      ∀ i, highCount α q ≤ degreeInto G (f ((selectedPaths P hp).parentCoreVertex i))
          (pool W Q S O sw D 0) ∧
        postponedCount α q ≤ degreeInto G (f ((selectedPaths P hp).parentCoreVertex i))
          (pool W Q S O sw D 1) := by
  obtain ⟨D⟩ := exists_data W Q S O sw hα hα1 hhost horder
  have hcore : ∃ f : (selectedPaths P hp).core.Copy (embeddingHost W),
      (∀ i, q ≤ G.degree (f (pathCorePartitionRoot P hp i)) ∧
        f (pathCorePartitionRoot P hp i) ∈ reservoir W Q (componentReservoirSide P i) ∧
        f (pathCorePartitionRoot P hp i) ∉ rootAvoid W Q S O sw D (componentReservoirSide P i)) ∧
      ∀ x, f x ∈ hostSupport W Q (fullMatching W Q S O sw) := by
    by_cases hminor : (fourthRoot α : ℝ) * q ≤ (branchMass P (sideBranches P 1) : ℝ)
    · obtain ⟨f, hroots, hsupp⟩ := exists_large_coreCopy W Q S hT P hp O sw hα hα1 hhost horder
        hcard hnot hminor (rootAvoid W Q S O sw D) (rootAvoid_card W Q S O sw D hα hα1 hhost horder)
      exact ⟨f, hroots, fun x => switched_hostSupport_subset_full W Q S P O sw (hsupp x)⟩
    · exact exists_small_coreCopy W Q S hT P hp O sw hα hα1 hhost horder hcard (lt_of_not_ge hminor)
        (rootAvoid W Q S O sw D) (rootAvoid_card W Q S O sw D hα hα1 hhost horder)
  obtain ⟨f, hroots, hsupp⟩ := hcore
  let original : (selectedPaths P hp).core.Copy G :=
    (SimpleGraph.Copy.ofLE (embeddingHost W) G (embeddingHost_le_original W)).comp f
  refine ⟨D, original, ?_, ?_⟩
  · intro s x hx
    exact Finset.disjoint_left.mp (pool_disjoint_hostSupport W Q S O sw D s) hx (hsupp x)
  · intro i
    have hroot := hroots (selectedRootIndex P hp i)
    rw [selected_parent_side] at hroot
    have hcount := pool_degree_counts W Q S O sw D hα hα1 hhost horder
      (reservoir_subset W Q 0 hroot.2.1) hroot.2.2
    rw [parentCore_eq_root W P hp]
    change highCount α q ≤ degreeInto G (f (pathCorePartitionRoot P hp (selectedRootIndex P hp i))) _ ∧
      postponedCount α q ≤ degreeInto G (f (pathCorePartitionRoot P hp (selectedRootIndex P hp i))) _
    exact ⟨hcount.1.trans (degreeInto_le_of_le G (embeddingHost W) (embeddingHost_le_original W) _ _),
      hcount.2.trans (degreeInto_le_of_le G (embeddingHost W) (embeddingHost_le_original W) _ _)⟩

end Erdos547b.ZhaoSourcePathCoreReady

#print axioms Erdos547b.ZhaoSourcePathCoreReady.parentCore_eq_root
#print axioms Erdos547b.ZhaoSourcePathCoreReady.exists_readyCore
