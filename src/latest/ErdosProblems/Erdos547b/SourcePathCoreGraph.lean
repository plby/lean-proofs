/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePathBranchRestriction
import ErdosProblems.Erdos547b.SourceRestrictedReconnectedGraph

/-! The literal postponed-path core in retained branch coordinates. -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePathCoreGraph

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourcePathBranchRestriction Erdos547b.ZhaoSourcePartitionReconnectedGraph
open Erdos547b.ZhaoSourcePartitionCutCoordinates Erdos547b.ZhaoSourceRestrictedCutCoordinates
open Erdos547b.ZhaoSourceReconnectedGraph Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoClaim68BranchAdapter Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim617CleanLoss Erdos547b.ZhaoClaim617CleanSelection
open Erdos547b.ZhaoClaim617RootPaths

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small p : ℕ} (P : ZhaoForestPartition T globalRoot small)
variable (hp : p ≤ (cleanBranches P).card)

theorem pathCore_retained_iff (x : U) :
    x ∉ (selectedPaths P hp).removedSet ↔
      retained (branchForest P) (keptBranches P hp) (cutBranchGraphIso P x) := by
  rw [retained_iff_not_removed]
  have hx : coordinateVertex P (cutBranchGraphIso P x) = x := by
    apply (cutBranchGraphIso P).injective
    exact cutBranchGraphIso_coordinateVertex P _
  rw [hx]

def pathCorePartitionRoot (i : Fin P.numParts) :
    {x // x ∉ (selectedPaths P hp).middleSet} :=
  (selectedPaths P hp).coreVertexEquiv.symm ⟨P.roots i, root_not_removed P hp i⟩

variable (hT : T.IsTree) {k : ℕ}
variable (locate : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 × Fin k)
variable (hlocate : ∀ i, (locate i).1 = componentReservoirSide P ((branchForest P).owner i))

def pathCoreCoordinateIso : T.induce {x | x ∉ (selectedPaths P hp).removedSet} ≃g
    (reconnectedGraph (branchForest P) (partitionCutSource P hT locate hlocate)).induce
      {x | retained (branchForest P) (keptBranches P hp) x} where
  toEquiv := (cutBranchGraphIso P).toEquiv.subtypeEquiv (pathCore_retained_iff P hp)
  map_rel_iff' := reconnected_adj_iff_tree P hT locate hlocate _ _

def pathCoreGraphIso : (selectedPaths P hp).core ≃g
    reconnectedGraph (OrderedBranchForest.restrict (branchForest P) (keptBranches P hp))
      (restrictCutSource (branchForest P) (keptBranches P hp) (componentReservoirSide P) locate
        (partitionCutSource P hT locate hlocate) (partitionParent_retained P hp)) :=
  (selectedPaths P hp).flatCoreIso.trans ((pathCoreCoordinateIso P hp hT locate hlocate).trans
    (restrictedReconnectedGraphIso (branchForest P) (keptBranches P hp) (componentReservoirSide P) locate
      (partitionCutSource P hT locate hlocate) (partitionParent_retained P hp)).symm)

theorem pathCoreGraphIso_root (i : Fin P.numParts) :
    pathCoreGraphIso P hp hT locate hlocate (pathCorePartitionRoot P hp i) = Sum.inl i := by
  apply coordinateInclusion_injective (branchForest P) (keptBranches P hp)
  change coordinateInclusion (branchForest P) (keptBranches P hp)
    (lowerCoordinate (branchForest P) (keptBranches P hp) (cutBranchGraphIso P (P.roots i)) _) = Sum.inl i
  exact (coordinateInclusion_lower (branchForest P) (keptBranches P hp) _ _).trans
    (cutBranchGraphIso_root P i)

theorem pathCoreGraphIso_parent (i : Fin p) :
    pathCoreGraphIso P hp hT locate hlocate ((selectedPaths P hp).parentCoreVertex i) =
      Sum.inl (selectedRootIndex P hp i) := by
  have heq : (selectedPaths P hp).parentCoreVertex i =
      pathCorePartitionRoot P hp (selectedRootIndex P hp i) := by
    apply Subtype.ext
    apply Subtype.ext
    exact selectedPaths_parent P hp i
  rw [heq, pathCoreGraphIso_root]

end Erdos547b.ZhaoSourcePathCoreGraph

#print axioms Erdos547b.ZhaoSourcePathCoreGraph.pathCoreGraphIso
#print axioms Erdos547b.ZhaoSourcePathCoreGraph.pathCoreGraphIso_parent
