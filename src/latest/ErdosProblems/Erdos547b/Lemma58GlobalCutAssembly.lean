/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GlobalCutOnline
import ErdosProblems.Erdos547b.Lemma58CutForestReconstruction

/-!
# Assembly of a synchronized online Lemma-5.8 state

The terminal synchronized state contains a complete dynamically oriented
embedding on every matching edge.  We paste those orientations, assemble the
literal branch forest, and use the retained online cut-parent adjacencies to
restore every edge deleted by the Zhao partition.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58GlobalCutAssembly

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma614Full
open Erdos547b.ZhaoLemma59FullOnline
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58ChosenMatchingAssembly
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalOwnerBranchImage
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58CutForestReconstruction

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The orientation retained by one terminal matching-edge state. -/
def terminalFiberOrient
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small) (G : SimpleGraph B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (S : OnlineOwnerPrefixState (branchForest P) G assign endpoint
      rootCandidate P.numParts)
    (e : Fin k) : Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2 :=
  (S.fullEdgeState (branchForest P) G assign endpoint rootCandidate e).orient

/-- Global branch orientation obtained by pasting the terminal edge-fiber
orientations. -/
def terminalOrient
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small) (G : SimpleGraph B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (S : OnlineOwnerPrefixState (branchForest P) G assign endpoint
      rootCandidate P.numParts) :
    Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 ≃ Fin 2 :=
  assembledOrient assign fun e ↦
    extendSelectedOrient (matchingFiber assign e)
      (terminalFiberOrient P G assign endpoint rootCandidate S e)

/-- One complete terminal edge fiber, reoriented by the pasted global
orientation without changing its graph copy. -/
noncomputable def terminalFiberEmbedding
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small) (G : SimpleGraph B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (S : OnlineOwnerPrefixState (branchForest P) G assign endpoint
      rootCandidate P.numParts)
    (e : Fin k) :
    DynamicAttachedForestEmbedding
      (onlineFiberForest (branchForest P) assign e) G
      (fun i ↦ S.rootImage
        (onlineFiberOwner (branchForest P) assign e i))
      (fun i ↦ terminalOrient P G assign endpoint rootCandidate S
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
      (endpoint e) := by
  let E := S.fullEdgeState (branchForest P) G assign endpoint rootCandidate e
  let Efull := E.state.toDynamic
    (onlineFiberForest (branchForest P) assign e) G
    (fun i ↦ S.rootImage
      (onlineFiberOwner (branchForest P) assign e i)) E.orient (endpoint e)
  exact reorientDynamic (onlineFiberForest (branchForest P) assign e) G
    (fun i ↦ S.rootImage
      (onlineFiberOwner (branchForest P) assign e i)) (endpoint e)
    E.orient
    (fun i ↦ terminalOrient P G assign endpoint rootCandidate S
      (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
    Efull (fun i ↦ by
      simp only [terminalOrient, assembledOrient_selectedEquiv,
        terminalFiberOrient, extendSelectedOrient_selectedEquiv, E])

/-- Deterministic assembly of the terminal edge states. -/
noncomputable def terminalRootAttachedBranchEmbedding
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small) (G : SimpleGraph B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (S : OnlineOwnerPrefixState (branchForest P) G assign endpoint
      rootCandidate P.numParts)
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1)) :
    RootAttachedBranchEmbedding (branchForest P) G S.rootImage
      (fun j c ↦ endpoint (assign j) c)
      (terminalOrient P G assign endpoint rootCandidate S) :=
  rootAttachedBranchEmbeddingOfMatchingFibers (branchForest P) G S.rootImage
    assign endpoint (terminalOrient P G assign endpoint rootCandidate S)
    (terminalFiberEmbedding P G assign endpoint rootCandidate S)
    hsupportDisjoint

/-- The assembled branch copy is literally the branch image stored in the
terminal synchronized state. -/
theorem terminalBranchCopy_eq_branchCopy
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small) (G : SimpleGraph B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (S : OnlineOwnerPrefixState (branchForest P) G assign endpoint
      rootCandidate P.numParts)
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (j : Fin (Fintype.card (ChildKey P.orderedForest)))
    (a : Fin ((branchForest P).branches.size j)) :
    (terminalRootAttachedBranchEmbedding P G assign endpoint rootCandidate S
        hsupportDisjoint).branchEmbedding.copy j a =
      OnlineOwnerPrefixState.branchCopy (branchForest P) G assign endpoint
        rootCandidate P.numParts S j ((branchForest P).owner j).isLt a := by
  unfold terminalRootAttachedBranchEmbedding
  change assembledBranchCopy (branchForest P) G S.rootImage assign endpoint
      (terminalOrient P G assign endpoint rootCandidate S)
      (terminalFiberEmbedding P G assign endpoint rootCandidate S) j a = _
  rw [assembledBranchCopy_apply]
  unfold terminalFiberEmbedding
  dsimp only [reorientDynamic,
    PartialDynamicAttachedForestEmbedding.toDynamic]
  erw [castChosenSelected_componentCopy]
  rfl

/-- Reconstruct the original tree from the terminal synchronized state.
Every deleted cut edge is supplied by the online adjacency recorded when its
child root was chosen. -/
noncomputable def treeCopyOfCutOnlineState
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (S : CutOnlineOwnerPrefixState P G assign endpoint rootCandidate
      P.numParts)
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hrootOutside : ∀ q e c, S.state.rootImage q ∉ endpoint e c) :
    T.Copy G := by
  classical
  let E := terminalRootAttachedBranchEmbedding P G assign endpoint
    rootCandidate S.state hsupportDisjoint
  have hrootInjective : Function.Injective S.state.rootImage := by
    intro q q' heq
    exact S.state.root_injective q q' q.isLt q'.isLt heq
  let branchCopy : (branchForest P).graph.Copy G :=
    E.toGraphCopy (branchForest P) G S.state.rootImage
      (fun j c ↦ endpoint (assign j) c)
      (terminalOrient P G assign endpoint rootCandidate S.state)
      hrootInjective (by
        intro q i a heq
        have hm := E.map_branch i a
        exact hrootOutside q (assign i)
          (terminalOrient P G assign endpoint rootCandidate S.state i
            ((branchForest P).branches.isTree i |>.coloringTwoOfVert
              ((branchForest P).branches.root i) a)) (heq.symm ▸ hm))
  let cutCopy : P.cutForest.Copy G :=
    branchCopy.comp (cutBranchGraphIso P).toCopy
  have hrootMap (q : Fin P.numParts) :
      cutCopy (P.roots q) = S.state.rootImage q := by
    change branchCopy (cutBranchGraphIso P (P.roots q)) = S.state.rootImage q
    rw [cutBranchGraphIso_root]
    change E.toGraphCopy (branchForest P) G S.state.rootImage
      (fun j c ↦ endpoint (assign j) c)
      (terminalOrient P G assign endpoint rootCandidate S.state)
      hrootInjective _ (Sum.inl q) = S.state.rootImage q
    rfl
  apply copy_of_cutForestCopy_of_cutAdj P cutCopy
  intro q hq
  have hadj := S.cut_adj q hq q.isLt
  by_cases hroot : P.parent q hq = P.roots (P.parentPart q hq)
  · rw [hrootMap, hroot, hrootMap]
    simpa [onlineCutParentImage, hroot] using hadj.symm
  · have hparentNonroot :=
      cutParent_mem_partitionNonroots P q hq hroot
    let z := cutParentBranchCoordinate P q hq hroot
    have hzval : (partitionBranchEquivNonroots P z).1 = P.parent q hq := by
      exact cutParentBranchCoordinate_value P q hq hroot
    have hparentMap :
        cutCopy (P.parent q hq) = E.branchEmbedding.copy z.1 z.2 := by
      change branchCopy (cutBranchGraphIso P (P.parent q hq)) = _
      rw [cutBranchGraphIso_nonroot P (P.parent q hq) hparentNonroot]
      change E.toGraphCopy (branchForest P) G S.state.rootImage
        (fun j c ↦ endpoint (assign j) c)
        (terminalOrient P G assign endpoint rootCandidate S.state)
        hrootInjective _ (Sum.inr
          ((partitionBranchEquivNonroots P).symm
            ⟨P.parent q hq, hparentNonroot⟩)) = _
      change E.branchEmbedding.copy
        ((partitionBranchEquivNonroots P).symm
          ⟨P.parent q hq, hparentNonroot⟩).1
        ((partitionBranchEquivNonroots P).symm
          ⟨P.parent q hq, hparentNonroot⟩).2 = _
      rfl
    rw [hrootMap, hparentMap]
    have hadj' : G.Adj
        (OnlineOwnerPrefixState.branchCopy (branchForest P) G assign endpoint
          rootCandidate P.numParts S.state z.1 (by
            rw [cutParentBranchCoordinate_owner P q hq hroot]
            exact (P.parentPart q hq).isLt) z.2)
        (S.state.rootImage q) := by
      simpa only [onlineCutParentImage, dif_neg hroot] using hadj
    rw [terminalBranchCopy_eq_branchCopy P G assign endpoint rootCandidate
      S.state hsupportDisjoint z.1 z.2]
    exact hadj'.symm

end Erdos547b.ZhaoLemma58GlobalCutAssembly

#print axioms Erdos547b.ZhaoLemma58GlobalCutAssembly.terminalBranchCopy_eq_branchCopy
#print axioms Erdos547b.ZhaoLemma58GlobalCutAssembly.treeCopyOfCutOnlineState
