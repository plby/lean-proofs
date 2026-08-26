/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLeafCoreGraph
import ErdosProblems.Erdos547b.SourceTerminalReconnectedCopy

/-!
# A literal leaf-core terminal state restores the entire original tree

The induced-core isomorphism retains every old root image. These are actual
high-degree vertices of the original host, so the checked leaf completion
adds every omitted original level-one leaf.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLeafTerminalTreeCopy

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceLeafCoreGraph Erdos547b.ZhaoSourceLeafBranchRestriction
open Erdos547b.ZhaoSourceTerminalReconnectedCopy Erdos547b.ZhaoSourceRestrictedCutCoordinates
open Erdos547b.ZhaoSourcePartitionCutCoordinates Erdos547b.ZhaoSourceCapacityGlobalPrefix
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim68ConcreteLeaves Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyAttachments

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ} (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
variable {k : ℕ} (locate : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 × Fin k)
variable (hlocate : ∀ i, (locate i).1 = componentReservoirSide P ((branchForest P).owner i))
variable (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin (keptBranches P).card))
variable (hcover : ∀ i, i ∈ family (restrictedLocate (keptBranches P) locate i).1
  (restrictedLocate (keptBranches P) locate i).2)
variable (A : CutPrefixState W Q S
  (OrderedBranchForest.restrict (branchForest P) (keptBranches P)).branches
  (OrderedBranchForest.restrict (branchForest P) (keptBranches P)).owner
  (componentReservoirSide P) kinds allocation family (restrictedLocate (keptBranches P) locate) hcover
  (restrictCutSource (branchForest P) (keptBranches P) (componentReservoirSide P) locate
    (partitionCutSource P hT locate hlocate) (partitionParent_retained P)) P.numParts)
variable (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
variable (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
  (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))

def actualLeafCoreCopy : (leafDeletedCore P).Copy (embeddingHost W) :=
  (terminalReconnectedCopy W Q S (OrderedBranchForest.restrict (branchForest P) (keptBranches P))
    (componentReservoirSide P) kinds allocation family (restrictedLocate (keptBranches P) locate) hcover _ A hdisjoint haway).comp
    (leafCoreGraphIso P hT locate hlocate).toCopy

theorem actualLeafCoreCopy_root_high (i : Fin P.numParts) :
    q ≤ G.degree (actualLeafCoreCopy W Q S P hT locate hlocate kinds allocation family hcover A hdisjoint haway
      (leafDeletedPartitionRoot P i)) := by
  change q ≤ G.degree (terminalReconnectedCopy W Q S _ _ _ _ _ _ _ _ A hdisjoint haway
    (leafCoreGraphIso P hT locate hlocate (leafDeletedPartitionRoot P i)))
  rw [leafCoreGraphIso_root]
  exact terminalReconnectedCopy_root_high W Q S _ _ _ _ _ _ _ _ A hdisjoint haway i

include A hdisjoint haway in
theorem exists_treeCopy_of_leafTerminal (hcard : Fintype.card U = q + 1) (hq : 2 ≤ q) :
    Nonempty (T.Copy G) := by
  have hc : 3 ≤ Fintype.card U := by omega
  let core := actualLeafCoreCopy W Q S P hT locate hlocate kinds allocation family hcover A hdisjoint haway
  let coreG := (SimpleGraph.Copy.ofLE (embeddingHost W) G (embeddingHost_le_original W)).comp core
  apply exists_copy_of_originalLevelOneLeaves_core P hT hc G coreG
  intro x
  obtain ⟨i, hi⟩ := originalLeafParent_eq_partitionRoot P hT x
  have hparent : (⟨originalLeafParent P hT x, originalLeafParent_not_mem P hT hc x⟩ : LeafDeletedVertex P) =
      leafDeletedPartitionRoot P i := Subtype.ext hi
  rw [hparent, hcard]
  change q ≤ G.degree (core (leafDeletedPartitionRoot P i))
  exact actualLeafCoreCopy_root_high W Q S P hT locate hlocate kinds allocation family hcover A hdisjoint haway i

end Erdos547b.ZhaoSourceLeafTerminalTreeCopy

#print axioms Erdos547b.ZhaoSourceLeafTerminalTreeCopy.actualLeafCoreCopy_root_high
#print axioms Erdos547b.ZhaoSourceLeafTerminalTreeCopy.exists_treeCopy_of_leafTerminal
