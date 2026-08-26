/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLeafCoreAllocation
import ErdosProblems.Erdos547b.SourceFreshPartitionBounds

/-!
# The original-level-one leaf bound from the actual source host

The two row totals construct disjoint core allocations. The resulting
reconnected copy preserves the original high-degree roots, so all deleted
leaves are restored by the checked leaf-completion theorem.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClaim68FromHost

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceLeafCoreNumerics Erdos547b.ZhaoSourceLeafCoreMass
open Erdos547b.ZhaoSourceLeafCoreAllocation
open Erdos547b.ZhaoSourceReconnectedTwoRowCopy Erdos547b.ZhaoTwoRowSurplusAllocation
open Erdos547b.ZhaoSourceLeafCoreGraph Erdos547b.ZhaoSourceLeafBranchRestriction
open Erdos547b.ZhaoSourceRestrictedCutCoordinates Erdos547b.ZhaoSourcePartitionCutCoordinates
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFreshPartitionBounds Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoClaim68ConcreteLeaves
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyAttachments Erdos547b.ZhaoClaim616HierarchyClassification

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U} (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))

include Q S hT in
theorem exists_treeCopy_of_manyOriginalLeaves
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hleaves : 11 * (fourthRoot α : ℝ) ^ 2 * q ≤ (originalLevelOneLeaves P).card) :
    Nonempty (T.Copy G) := by
  let F := OrderedBranchForest.restrict (branchForest P) (keptBranches P)
  let rootSide := componentReservoirSide P
  let locate := sideLocate (branchForest P) rootSide
  let L := restrictCutSource (branchForest P) (keptBranches P) rootSide locate
    (partitionCutSource P hT locate (fun _ => rfl)) (partitionParent_retained P)
  obtain ⟨E, hdis, haway, hbudget⟩ := exists_coreAllocation P W Q S hT hα hα1 hhost horder hcard hleaves
  have hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
    subst hostN
    exact freshPartition_root_bound hα hα1 W horder hcard P
  obtain ⟨f, hf⟩ := exists_reconnectedCopy_of_twoRowBudgets W Q S F rootSide L hα hα1 hhost horder
    E hdis haway
    (fun i => canonical_branch_size_le_small P (OrderedBranchForest.selectedEquiv (keptBranches P) i))
    hroots (fun s _ => hbudget s)
  let core := f.comp (leafCoreGraphIso P hT locate (fun _ => rfl)).toCopy
  let coreG := (SimpleGraph.Copy.ofLE (embeddingHost W) G (embeddingHost_le_original W)).comp core
  have hq : 2 ≤ q := by
    have hw := W.five_ordinaryParts_le_host
    have hp := W.ordinaryParts_pos
    omega
  have hc : 3 ≤ Fintype.card U := by omega
  apply exists_copy_of_originalLevelOneLeaves_core P hT hc G coreG
  intro x
  obtain ⟨i, hi⟩ := originalLeafParent_eq_partitionRoot P hT x
  have hparent : (⟨originalLeafParent P hT x, originalLeafParent_not_mem P hT hc x⟩ : LeafDeletedVertex P) =
      leafDeletedPartitionRoot P i := Subtype.ext hi
  rw [hparent, hcard]
  change q ≤ G.degree (f (leafCoreGraphIso P hT locate (fun _ => rfl) (leafDeletedPartitionRoot P i)))
  exact Eq.mpr (congrArg (fun v : F.Vertex => q ≤ G.degree (f v))
    (leafCoreGraphIso_root P hT locate (fun _ => rfl) i)) (hf i)

include Q S hT in
theorem originalLevelOneLeaves_lt_of_not_copy
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G) :
    ((originalLevelOneLeaves P).card : ℝ) < 11 * (fourthRoot α : ℝ) ^ 2 * q := by
  apply lt_of_not_ge
  intro hleaves
  obtain ⟨E⟩ := exists_treeCopy_of_manyOriginalLeaves W Q S hT P hα hα1 hhost horder hcard hleaves
  exact hnot E.isContained

end Erdos547b.ZhaoSourceClaim68FromHost

#print axioms Erdos547b.ZhaoSourceClaim68FromHost.exists_treeCopy_of_manyOriginalLeaves
#print axioms Erdos547b.ZhaoSourceClaim68FromHost.originalLevelOneLeaves_lt_of_not_copy
