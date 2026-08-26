/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLeafBranchRestriction
import ErdosProblems.Erdos547b.SourceRestrictedReconnectedGraph

/-!
# The actual leaf-deleted core is the reconnected retained branch graph

The isomorphism keeps every original component root at its original index.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLeafCoreGraph

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceLeafBranchRestriction Erdos547b.ZhaoSourcePartitionReconnectedGraph
open Erdos547b.ZhaoSourcePartitionCutCoordinates Erdos547b.ZhaoSourceRestrictedCutCoordinates
open Erdos547b.ZhaoSourceReconnectedGraph Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoClaim68ConcreteLeaves Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyAttachments

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ} (P : ZhaoForestPartition T globalRoot small)
variable (hT : T.IsTree) {k : ℕ}
variable (locate : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 × Fin k)
variable (hlocate : ∀ i, (locate i).1 = componentReservoirSide P ((branchForest P).owner i))

theorem leafCore_retained_iff (x : U) : x ∉ originalLevelOneLeaves P ↔
    retained (branchForest P) (keptBranches P) (cutBranchGraphIso P x) := by
  rw [retained_iff_not_originalLeaves]
  have hx : coordinateVertex P (cutBranchGraphIso P x) = x := by
    apply (cutBranchGraphIso P).injective
    exact cutBranchGraphIso_coordinateVertex P _
  rw [hx]

def leafCoreCoordinateIso : leafDeletedCore P ≃g
    (reconnectedGraph (branchForest P) (partitionCutSource P hT locate hlocate)).induce
      {x | retained (branchForest P) (keptBranches P) x} where
  toEquiv := (cutBranchGraphIso P).toEquiv.subtypeEquiv (leafCore_retained_iff P)
  map_rel_iff' := reconnected_adj_iff_tree P hT locate hlocate _ _

def leafCoreGraphIso : leafDeletedCore P ≃g
    reconnectedGraph (OrderedBranchForest.restrict (branchForest P) (keptBranches P))
      (restrictCutSource (branchForest P) (keptBranches P) (componentReservoirSide P) locate
        (partitionCutSource P hT locate hlocate) (partitionParent_retained P)) :=
  (leafCoreCoordinateIso P hT locate hlocate).trans
    (restrictedReconnectedGraphIso (branchForest P) (keptBranches P) (componentReservoirSide P) locate
      (partitionCutSource P hT locate hlocate) (partitionParent_retained P)).symm

theorem leafCoreGraphIso_root (i : Fin P.numParts) :
    leafCoreGraphIso P hT locate hlocate (leafDeletedPartitionRoot P i) = Sum.inl i := by
  apply coordinateInclusion_injective (branchForest P) (keptBranches P)
  change coordinateInclusion (branchForest P) (keptBranches P)
    (lowerCoordinate (branchForest P) (keptBranches P) (cutBranchGraphIso P (P.roots i)) _) = Sum.inl i
  exact (coordinateInclusion_lower (branchForest P) (keptBranches P) _ _).trans (cutBranchGraphIso_root P i)

end Erdos547b.ZhaoSourceLeafCoreGraph

#print axioms Erdos547b.ZhaoSourceLeafCoreGraph.leafCoreGraphIso
#print axioms Erdos547b.ZhaoSourceLeafCoreGraph.leafCoreGraphIso_root
