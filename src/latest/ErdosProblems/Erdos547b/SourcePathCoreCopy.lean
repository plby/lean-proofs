/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePathCoreAllocation
import ErdosProblems.Erdos547b.SourceMatchingTwoRowCopy
import ErdosProblems.Erdos547b.SourceFreshPartitionBounds

/-! # The literal large-minor postponed core is actually copied -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePathCoreCopy

open Finset SimpleGraph Erdos547b.TreePartition Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFreshPartitionBounds Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceClaim617PathNumerics Erdos547b.ZhaoSourcePathCoreMass
open Erdos547b.ZhaoSourcePathCoreGraph Erdos547b.ZhaoSourcePathBranchRestriction
open Erdos547b.ZhaoSourcePathCoreAllocation Erdos547b.ZhaoClaim617CleanLoss
open Erdos547b.ZhaoClaim617CleanSelection Erdos547b.ZhaoClaim617RootPaths
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceClaim617Switch
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoSourceMatchingTwoRowCopy
open Erdos547b.ZhaoSourceMatchingCopySupport Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceRestrictedCutCoordinates Erdos547b.ZhaoSourcePartitionCutCoordinates
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoSourceReconnectedTwoRowCopy (sideLocate)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U} (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (hp : postponedCount α q ≤ (cleanBranches P).card)
variable (O : Output W Q S (branchMass P (sideBranches P 1))) (sw : Switch W Q S O)

include hT in
theorem exists_large_coreCopy
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G)
    (hminor : (fourthRoot α : ℝ) * q ≤ (branchMass P (sideBranches P 1) : ℝ))
    (avoid : Fin 2 → Finset (Fin hostN))
    (havoid : ∀ s, ((avoid s).card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * W.clusterSize) :
    ∃ f : (selectedPaths P hp).core.Copy (embeddingHost W),
      (∀ i, q ≤ G.degree (f (pathCorePartitionRoot P hp i)) ∧
        f (pathCorePartitionRoot P hp i) ∈ reservoir W Q (componentReservoirSide P i) ∧
        f (pathCorePartitionRoot P hp i) ∉ avoid (componentReservoirSide P i)) ∧
      ∀ x, f x ∈ hostSupport W Q sw.switched := by
  let F := coreForest P hp
  let rootSide := componentReservoirSide P
  let locate := sideLocate (branchForest P) rootSide
  let L := restrictCutSource (branchForest P) (keptBranches P hp) rootSide locate
    (partitionCutSource P hT locate (fun _ => rfl)) (partitionParent_retained P hp)
  obtain ⟨E, hdis, haway, hbudget⟩ := exists_large_coreAllocation W Q S hT P hp O sw
    hα hα1 hhost horder hcard hnot hminor
  have hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
    subst hostN
    exact freshPartition_root_bound hα hα1 W horder hcard P
  obtain ⟨f, hf, hsupport⟩ := exists_reconnectedCopy_of_twoRowBudgets W Q S sw.switched F rootSide L
    (switched_properties W Q S O sw).1 hα hα1 hhost horder E hdis haway
    (fun i => canonical_branch_size_le_small P (OrderedBranchForest.selectedEquiv (keptBranches P hp) i))
    hroots avoid havoid (fun s _ => hbudget s)
  let core := f.comp (pathCoreGraphIso P hp hT locate (fun _ => rfl)).toCopy
  have hmap (i : Fin P.numParts) : core (pathCorePartitionRoot P hp i) = f (Sum.inl i) :=
    congrArg f (pathCoreGraphIso_root P hp hT locate (fun _ => rfl) i)
  refine ⟨core, ?_, ?_⟩
  · intro i
    rw [hmap]
    exact hf i
  · intro x
    exact hsupport _

end Erdos547b.ZhaoSourcePathCoreCopy

#print axioms Erdos547b.ZhaoSourcePathCoreCopy.exists_large_coreCopy
