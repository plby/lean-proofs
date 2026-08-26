/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityTerminalBranches
import ErdosProblems.Erdos547b.SourceCapacityGlobalCutPrefix
import ErdosProblems.Erdos547b.SourcePartitionCutCoordinates
import ErdosProblems.Erdos547b.Lemma58CutForestReconstruction

/-!
# The literal tree copy from concrete capacity-aware source budgets

The terminal state is constructed by the actual mixed-kind root and
family induction. Reuse the existing source partition isomorphism and
cut-edge reconstruction, retaining every root and branch image.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityTerminalTreeCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.TreePartition
open Erdos547b.ZhaoSourceCapacityGlobalPrefix Erdos547b.ZhaoSourcePartitionCutCoordinates
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoClaim68 Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyAttachments Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma614Full Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoSourceGlobalPrefixState (CutCoordinate coordinateOwner)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small) {k : ℕ}
variable (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin (Fintype.card (ChildKey P.orderedForest))))
variable (locate : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∈ family (locate i).1 (locate i).2)
variable (hlocate : ∀ i, (locate i).1 = componentReservoirSide P ((branchForest P).owner i))

def terminalTreeCopy
    (A : CutPrefixState W Q S (branchForest P).branches (branchForest P).owner
      (componentReservoirSide P) kinds allocation family locate hcover (partitionCutSource P hT locate hlocate) P.numParts)
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
    (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)) : T.Copy (embeddingHost W) := by
  let E := A.state.terminalBranchEmbedding W Q S (branchForest P).branches (branchForest P).owner
    (componentReservoirSide P) kinds allocation family locate hcover hdisjoint
  have hroot : Function.Injective A.state.rootImage :=
    fun i j h => A.state.root_injective i j i.isLt j.isLt h
  let graphCopy := (branchForest P).copyOfBranchEmbedding (embeddingHost W) A.state.rootImage E hroot
    (A.state.root_ne_branchCopy W Q S (branchForest P).branches (branchForest P).owner
      (componentReservoirSide P) kinds allocation family locate hcover haway)
    (fun i => A.state.branchCopy_attach W Q S (branchForest P).branches (branchForest P).owner
      (componentReservoirSide P) kinds allocation family locate hcover i ((branchForest P).owner i).isLt)
  let cutCopy : P.cutForest.Copy (embeddingHost W) := graphCopy.comp (cutBranchGraphIso P).toCopy
  have hrootMap (i : Fin P.numParts) : cutCopy (P.roots i) = A.state.rootImage i := by
    change graphCopy (cutBranchGraphIso P (P.roots i)) = _
    rw [cutBranchGraphIso_root]
    rfl
  have hcoordinateMap (x : CutCoordinate (branchForest P).branches P.numParts) :
      cutCopy (coordinateVertex P x) =
        A.state.coordinateImage (branchForest P).branches (branchForest P).owner W Q S
          (componentReservoirSide P) kinds allocation family locate hcover x
          (coordinateOwner (branchForest P).branches (branchForest P).owner x).isLt := by
    cases x with
    | inl i => exact hrootMap i
    | inr a =>
        change graphCopy (cutBranchGraphIso P (partitionBranchEquivNonroots P a).1) = _
        rw [cutBranchGraphIso_nonroot P _ (partitionBranchEquivNonroots P a).2]
        change graphCopy (Sum.inr ((partitionBranchEquivNonroots P).symm (partitionBranchEquivNonroots P a))) = _
        rw [(partitionBranchEquivNonroots P).symm_apply_apply]
        rfl
  apply copy_of_cutForestCopy_of_cutAdj P cutCopy
  intro i hi
  have hp := hcoordinateMap (partitionParent P i hi)
  rw [partitionParent_vertex] at hp
  rw [hrootMap i, hp]
  exact (A.cut_adj i hi i.isLt).symm

include hT locate hcover in
/-- Every host image and cut edge is constructed internally. The inputs
are the actual finite source partition, classified disjoint allocations,
and their explicit scalar capacity budgets. -/
theorem exists_treeCopy_of_sourceBudgets
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
    (hkind : ∀ s j, (kinds s j).Valid α)
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => (branchForest P).owner i ≤ (branchForest P).owner j))
    (hside : ∀ s j i, i ∈ family s j → componentReservoirSide P ((branchForest P).owner i) = s)
    (hbranch : ∀ s j, ∀ i ∈ family s j, (kinds s j).BranchValid (branchForest P).branches i)
    (hedge : ∀ s j, ∀ e ∈ allocation s j, edgeValid W Q S (rootCluster W Q s) (kinds s j) e)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
    (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (globalCount : ℕ) (hglobal : ∀ s, (Finset.univ.biUnion (allocation s)).card ≤ globalCount)
    (hbudget : ∀ s j, family s j ≠ [] → mass (fun i => ((branchForest P).branches.size i : ℝ)) (family s j) ≤
      (∑ e ∈ allocation s j, capacity W Q S (rootCluster W Q s) (kinds s j) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (allocation s j).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  have hlocate : ∀ i, (locate i).1 = componentReservoirSide P ((branchForest P).owner i) :=
    fun i => (hside (locate i).1 (locate i).2 i (hcover i)).symm
  have hsameSide (s : Fin 2) : Pairwise (fun i j => Disjoint (allocation s i) (allocation s j)) := by
    intro i j hne
    exact hdisjoint ⟨s, i⟩ ⟨s, j⟩ (fun h => hne (congrArg Prod.snd h))
  obtain ⟨A⟩ := exists_terminalCutPrefix W Q S (branchForest P).branches (branchForest P).owner
    (componentReservoirSide P) kinds allocation family locate hcover (partitionCutSource P hT locate hlocate)
    hα hα1 hhost horder hk hkind hsameSide hside hbranch hedge hsmall haway
    globalCount hglobal hbudget hroots hnd hordered
  exact ⟨terminalTreeCopy W Q S hT P kinds allocation family locate hcover hlocate A hdisjoint haway⟩

end Erdos547b.ZhaoSourceCapacityTerminalTreeCopy

#print axioms Erdos547b.ZhaoSourceCapacityTerminalTreeCopy.terminalTreeCopy
#print axioms Erdos547b.ZhaoSourceCapacityTerminalTreeCopy.exists_treeCopy_of_sourceBudgets
