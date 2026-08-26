/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedTerminalBranches
import ErdosProblems.Erdos547b.SourceMarkedGlobalCutPrefix
import ErdosProblems.Erdos547b.SourcePartitionMarkedCoordinates
import ErdosProblems.Erdos547b.Lemma58CutForestReconstruction

/-!
# Extracting the original tree from the terminal combined cut-prefix

All branch and root images are retained. The source cut-forest isomorphism
transports the globally injective combined embedding, and actual cut edges
restore the original tree.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedTerminalTreeCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.TreePartition
open Erdos547b.ZhaoSourceMarkedGlobalPrefix Erdos547b.ZhaoSourcePartitionCutCoordinates
open Erdos547b.ZhaoSourcePartitionCutMarks Erdos547b.ZhaoSourcePrivatePairGeometry
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoClaim68 Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyAttachments Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma614Full Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoSourceGlobalPrefixState (CutCoordinate coordinateOwner)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (sourceP : ZhaoForestPartition T globalRoot small) {k : ℕ}
variable (selected : Finset (Fin (Fintype.card (ChildKey sourceP.orderedForest))))
variable (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin (Fintype.card (ChildKey sourceP.orderedForest))))
variable (locate : Fin (Fintype.card (ChildKey sourceP.orderedForest)) → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∉ selected → i ∈ family (locate i).1 (locate i).2)
variable (hlocate : ∀ i, (locate i).1 = componentReservoirSide sourceP ((branchForest sourceP).owner i))

def terminalTreeCopy
    (A : CutPrefixState W Q S O P (branchForest sourceP).branches (branchForest sourceP).owner
      (branchMarks sourceP) selected (componentReservoirSide sourceP) kinds allocation family locate hcover
      (partitionCutSource sourceP hT locate hlocate) sourceP.numParts)
    (hCV1 : C ⊆ O.D.V1)
    (hresidual : ∀ s j e, e ∈ allocation s j →
      e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges)
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
    (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)) : T.Copy (embeddingHost W) := by
  let E := A.state.terminalBranchEmbedding W Q S O P (branchForest sourceP).branches (branchForest sourceP).owner
    (branchMarks sourceP) selected (componentReservoirSide sourceP) kinds allocation family locate hcover hCV1 hresidual hdisjoint
  have hroot : Function.Injective A.state.ordinary.rootImage :=
    fun i j h => A.state.ordinary.root_injective i j i.isLt j.isLt h
  let graphCopy := (branchForest sourceP).copyOfBranchEmbedding (embeddingHost W) A.state.ordinary.rootImage E hroot
    (A.state.root_ne_branchCopy W Q S O P (branchForest sourceP).branches (branchForest sourceP).owner
      (branchMarks sourceP) selected (componentReservoirSide sourceP) kinds allocation family locate hcover hCV1 haway)
    (fun i => A.state.branchCopy_attach W Q S O P (branchForest sourceP).branches (branchForest sourceP).owner
      (branchMarks sourceP) selected (componentReservoirSide sourceP) kinds allocation family locate hcover i
      ((branchForest sourceP).owner i).isLt)
  let cutCopy : sourceP.cutForest.Copy (embeddingHost W) := graphCopy.comp (cutBranchGraphIso sourceP).toCopy
  have hrootMap (i : Fin sourceP.numParts) : cutCopy (sourceP.roots i) = A.state.ordinary.rootImage i := by
    change graphCopy (cutBranchGraphIso sourceP (sourceP.roots i)) = _
    rw [cutBranchGraphIso_root]
    rfl
  have hcoordinateMap (x : CutCoordinate (branchForest sourceP).branches sourceP.numParts) :
      cutCopy (coordinateVertex sourceP x) =
        A.state.coordinateImage (branchForest sourceP).branches (branchForest sourceP).owner
          (branchMarks sourceP) selected W Q S O P (componentReservoirSide sourceP) kinds allocation family locate hcover x
          (coordinateOwner (branchForest sourceP).branches (branchForest sourceP).owner x).isLt := by
    cases x with
    | inl i => exact hrootMap i
    | inr a =>
        change graphCopy (cutBranchGraphIso sourceP (partitionBranchEquivNonroots sourceP a).1) = _
        rw [cutBranchGraphIso_nonroot sourceP _ (partitionBranchEquivNonroots sourceP a).2]
        change graphCopy (Sum.inr ((partitionBranchEquivNonroots sourceP).symm (partitionBranchEquivNonroots sourceP a))) = _
        rw [(partitionBranchEquivNonroots sourceP).symm_apply_apply]
        rfl
  apply copy_of_cutForestCopy_of_cutAdj sourceP cutCopy
  intro i hi
  have hp := hcoordinateMap (partitionParent sourceP i hi)
  rw [partitionParent_vertex] at hp
  rw [hrootMap i, hp]
  exact (A.cut_adj i hi i.isLt).symm

end Erdos547b.ZhaoSourceMarkedTerminalTreeCopy

#print axioms Erdos547b.ZhaoSourceMarkedTerminalTreeCopy.terminalTreeCopy
