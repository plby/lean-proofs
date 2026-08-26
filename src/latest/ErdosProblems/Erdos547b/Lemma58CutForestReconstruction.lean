/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58CertifiedMatchingAssembly
import ErdosProblems.Erdos547b.Claim617BranchCount
import ErdosProblems.Erdos547b.Lemma614
import ErdosProblems.Erdos547b.Lemma59FullOnline
import ErdosProblems.Erdos547b.Claim616HierarchyClassification

/-!
# Reconstructing Zhao's cut forest from certified Lemma-5.8 fibers

The root-deleted branches form a graph canonically isomorphic to the Zhao
cut forest.  An owner-specific forbidden set records the non-neighbours of
every later component root whose deleted parent lies in that owner.  Hence
the certificate retained by `Lemma58CertifiedMatchingAssembly` supplies all
missing cut-parent adjacencies, while root-to-root cut edges are handled by
the distinguished root reservoirs.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58CutForestReconstruction

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim68BranchGraphTransport
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58CertifiedMatchingAssembly
open Erdos547b.ZhaoLemma614Full
open Erdos547b.ZhaoLemma59FullOnline
open Erdos547b.ZhaoClaim616HierarchyClassification

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Canonical graph isomorphism from the literal Zhao cut forest to its
component-root / root-deleted-branch presentation. -/
noncomputable def cutBranchGraphIso
    (P : ZhaoForestPartition T globalRoot small) :
    P.cutForest ≃g (branchForest P).graph :=
  (cutForestGraphIso P).trans (branchGraphIso P.orderedForest).symm

@[simp] theorem cutBranchGraphIso_root
    (P : ZhaoForestPartition T globalRoot small) (q : Fin P.numParts) :
    cutBranchGraphIso P (P.roots q) = Sum.inl q := by
  change (branchGraphIso P.orderedForest).symm
      (cutForestGraphIso P (P.roots q)) = Sum.inl q
  apply (branchGraphIso P.orderedForest).injective
  rw [(branchGraphIso P.orderedForest).apply_symm_apply]
  change P.toOrderedForestVertex (P.roots q) =
    flattenBranch P.orderedForest (Sum.inl q)
  rw [Erdos547b.ZhaoLemma614Full.toOrderedForestVertex_root,
    flattenBranch_root]

@[simp] theorem cutBranchGraphIso_nonroot
    (P : ZhaoForestPartition T globalRoot small) (x : V)
    (hx : x ∈ partitionNonroots P) :
    cutBranchGraphIso P x =
      Sum.inr ((partitionBranchEquivNonroots P).symm ⟨x, hx⟩) := by
  change (branchGraphIso P.orderedForest).symm (cutForestGraphIso P x) = _
  apply (branchGraphIso P.orderedForest).injective
  rw [(branchGraphIso P.orderedForest).apply_symm_apply]
  change P.toOrderedForestVertex x =
    flattenBranch P.orderedForest
      (Sum.inr ((partitionBranchEquivNonroots P).symm ⟨x, hx⟩))
  apply Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P
  rw [P.from_toOrderedForestVertex]
  have hz := (partitionBranchEquivNonroots P).apply_symm_apply ⟨x, hx⟩
  exact congrArg Subtype.val hz |>.symm

/-- Vertices on one physical matching endpoint which fail adjacency to at
least one later component root whose deleted parent lies in owner `q`. -/
def cutParentBad
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (q : Fin P.numParts) (c : Fin 2) : Finset B :=
  (endpoint e c).filter fun x ↦
    ∃ j : Fin P.numParts, ∃ hj : j.val ≠ 0,
      P.parentPart j hj = q ∧
      P.parent j hj ≠ P.roots q ∧
      ¬ G.Adj (rootImage j) x

@[simp] theorem mem_cutParentBad
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (q : Fin P.numParts) (c : Fin 2) (x : B) :
    x ∈ cutParentBad P G rootImage endpoint e q c ↔
      x ∈ endpoint e c ∧
      ∃ j : Fin P.numParts, ∃ hj : j.val ≠ 0,
        P.parentPart j hj = q ∧
        P.parent j hj ≠ P.roots q ∧
        ¬ G.Adj (rootImage j) x := by
  simp [cutParentBad]

/-- Noninitial partition indices, i.e. the indices of deleted cut edges. -/
abbrev CutIndex (P : ZhaoForestPartition T globalRoot small) :=
  {j : Fin P.numParts // j.val ≠ 0}

/-- Later component roots whose non-root cut parent lies in owner `q`. -/
def internalCutChildren (P : ZhaoForestPartition T globalRoot small)
    (q : Fin P.numParts) : Finset (CutIndex P) :=
  Finset.univ.filter fun j ↦
    P.parentPart j.1 j.2 = q ∧ P.parent j.1 j.2 ≠ P.roots q

/-- The non-neighbours in one physical endpoint of one later root. -/
def cutRootNonneighbors
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (c : Fin 2) (j : CutIndex P) : Finset B :=
  (endpoint e c).filter fun x ↦ ¬ G.Adj (rootImage j.1) x

/-- The owner-specific bad set is covered by the union of the literal
non-neighbour sets of its internal cut children. -/
theorem cutParentBad_subset_biUnion
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (q : Fin P.numParts) (c : Fin 2) :
    cutParentBad P G rootImage endpoint e q c ⊆
      (internalCutChildren P q).biUnion
        (cutRootNonneighbors P G rootImage endpoint e c) := by
  classical
  intro x hx
  obtain ⟨hxEndpoint, j, hj, hpart, hnotroot, hnotAdj⟩ :=
    (mem_cutParentBad P G rootImage endpoint e q c x).mp hx
  let z : CutIndex P := ⟨j, hj⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨z, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpart, hnotroot⟩
  · exact Finset.mem_filter.mpr ⟨hxEndpoint, hnotAdj⟩

/-- Union-bound form of the target-cleaning loss.  Only roots whose actual
non-root cut parent lies in `q` are charged. -/
theorem card_cutParentBad_le
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (q : Fin P.numParts) (c : Fin 2) (loss : ℕ)
    (htypical : ∀ j ∈ internalCutChildren P q,
      #(cutRootNonneighbors P G rootImage endpoint e c j) ≤ loss) :
    #(cutParentBad P G rootImage endpoint e q c) ≤
        #(internalCutChildren P q) * loss := by
  calc
    #(cutParentBad P G rootImage endpoint e q c) ≤
        #((internalCutChildren P q).biUnion
          (cutRootNonneighbors P G rootImage endpoint e c)) :=
      Finset.card_le_card
        (cutParentBad_subset_biUnion P G rootImage endpoint e q c)
    _ ≤ ∑ j ∈ internalCutChildren P q,
        #(cutRootNonneighbors P G rootImage endpoint e c j) :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ internalCutChildren P q, loss := by
      exact Finset.sum_le_sum fun j hj ↦ htypical j hj
    _ = #(internalCutChildren P q) * loss := by
      simp [Finset.sum_const]

/-- Coarser but convenient bound charging at most all partition roots. -/
theorem card_cutParentBad_le_numParts_mul
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (q : Fin P.numParts) (c : Fin 2) (loss : ℕ)
    (htypical : ∀ j ∈ internalCutChildren P q,
      #(cutRootNonneighbors P G rootImage endpoint e c j) ≤ loss) :
    #(cutParentBad P G rootImage endpoint e q c) ≤ P.numParts * loss := by
  calc
    #(cutParentBad P G rootImage endpoint e q c) ≤
        #(internalCutChildren P q) * loss :=
      card_cutParentBad_le P G rootImage endpoint e q c loss htypical
    _ ≤ P.numParts * loss := by
      apply Nat.mul_le_mul_right loss
      calc
        #(internalCutChildren P q) ≤ Fintype.card (CutIndex P) := by
          simpa only [Finset.card_univ] using
            Finset.card_le_card (Finset.subset_univ (internalCutChildren P q))
        _ ≤ Fintype.card (Fin P.numParts) :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        _ = P.numParts := Fintype.card_fin _

/-- A graph copy remains a copy after enlarging the target graph on the same
vertex type. -/
def graphCopy_mono
    {A B : Type*} {F : SimpleGraph A} {G H : SimpleGraph B}
    (hGH : G ≤ H) (C : F.Copy G) : F.Copy H where
  toHom := {
    toFun := C
    map_rel' := by
      intro a b hab
      exact hGH (C.toHom.map_rel hab)
  }
  injective' := C.injective

/-- A certified matching-fiber realization, whose bad sets are exactly the
cut-parent non-neighbours, reconstructs the original tree once root/root cut
edges and root/branch collisions are discharged. -/
noncomputable def treeCopyOfCertifiedMatchingFibersOfLE
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (hGle : Gpair ≤ Gtarget)
    {k : ℕ} (rootImage : Fin P.numParts → B)
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (E : CertifiedRootAttachedBranchEmbedding (branchForest P) Gpair rootImage
      assign endpoint (cutParentBad P Gtarget rootImage endpoint))
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ q e c, rootImage q ∉ endpoint e c)
    (hrootCut : ∀ j (hj : j.val ≠ 0),
      P.parent j hj = P.roots (P.parentPart j hj) →
      Gtarget.Adj (rootImage j) (rootImage (P.parentPart j hj))) :
    T.Copy Gtarget := by
  classical
  let branchCopyPair : (branchForest P).graph.Copy Gpair :=
    E.embedding.toGraphCopy (branchForest P) Gpair rootImage
      (fun j c ↦ endpoint (assign j) c) E.orient hrootInjective (by
        intro q i a heq
        have hm := E.embedding.map_branch i a
        exact hrootOutside q (assign i)
          (E.orient i ((branchForest P).branches.isTree i |>.coloringTwoOfVert
            ((branchForest P).branches.root i) a)) (heq.symm ▸ hm))
  let branchCopy : (branchForest P).graph.Copy Gtarget :=
    graphCopy_mono hGle branchCopyPair
  let cutCopy : P.cutForest.Copy Gtarget :=
    branchCopy.comp (cutBranchGraphIso P).toCopy
  have hrootMap (q : Fin P.numParts) :
      cutCopy (P.roots q) = rootImage q := by
    change branchCopy (cutBranchGraphIso P (P.roots q)) = rootImage q
    rw [cutBranchGraphIso_root]
    change branchCopyPair (Sum.inl q) = rootImage q
    rfl
  apply copy_of_cutForestCopy_of_cutAdj P cutCopy
  intro j hj
  by_cases hroot : P.parent j hj = P.roots (P.parentPart j hj)
  · rw [hrootMap, hroot, hrootMap]
    exact hrootCut j hj hroot
  · have hparentNonroot : P.parent j hj ∈ partitionNonroots P := by
      rw [partitionNonroots, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hp
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hp
      have hipart : i = P.parentPart j hj := by
        calc
          i = P.componentIndex (P.roots i) :=
            (componentIndex_roots P i).symm
          _ = P.componentIndex (P.parent j hj) := congrArg P.componentIndex hi
          _ = P.parentPart j hj := componentIndex_parent P j hj
      subst i
      exact hroot hi.symm
    let z : Σ t, Fin ((branchForest P).branches.size t) :=
      (partitionBranchEquivNonroots P).symm
        ⟨P.parent j hj, hparentNonroot⟩
    have hzval : (partitionBranchEquivNonroots P z).1 = P.parent j hj := by
      exact congrArg Subtype.val
        ((partitionBranchEquivNonroots P).apply_symm_apply
          ⟨P.parent j hj, hparentNonroot⟩)
    have howner : P.parentPart j hj = (branchForest P).owner z.1 := by
      have hc := partitionBranchEquivNonroots_component P z
      rw [hzval, componentIndex_parent P j hj] at hc
      exact hc
    have hparentMap :
        cutCopy (P.parent j hj) =
          E.embedding.branchEmbedding.copy z.1 z.2 := by
      change branchCopy (cutBranchGraphIso P (P.parent j hj)) = _
      rw [cutBranchGraphIso_nonroot P (P.parent j hj) hparentNonroot]
      change branchCopyPair (Sum.inr z) = _
      rfl
    rw [hrootMap, hparentMap]
    by_contra hnotAdj
    have hmem := E.embedding.map_branch z.1 z.2
    have hroot' : P.parent j hj ≠
        P.roots ((branchForest P).owner z.1) := by
      simpa only [howner] using hroot
    have hbad : E.embedding.branchEmbedding.copy z.1 z.2 ∈
        cutParentBad P Gtarget rootImage endpoint (assign z.1)
          ((branchForest P).owner z.1)
          (E.orient z.1
            ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
              ((branchForest P).branches.root z.1) z.2)) := by
      apply (mem_cutParentBad P Gtarget rootImage endpoint _ _ _ _).2
      refine ⟨hmem, j, hj, howner, hroot', ?_⟩
      exact hnotAdj
    exact E.avoids z.1 z.2 hbad

/-- Same-graph specialization of the preceding ambient-target constructor. -/
noncomputable def treeCopyOfCertifiedMatchingFibers
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ} (rootImage : Fin P.numParts → B)
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (E : CertifiedRootAttachedBranchEmbedding (branchForest P) G rootImage
      assign endpoint (cutParentBad P G rootImage endpoint))
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ q e c, rootImage q ∉ endpoint e c)
    (hrootCut : ∀ j (hj : j.val ≠ 0),
      P.parent j hj = P.roots (P.parentPart j hj) →
      G.Adj (rootImage j) (rootImage (P.parentPart j hj))) :
    T.Copy G :=
  treeCopyOfCertifiedMatchingFibersOfLE P G G le_rfl rootImage assign
    endpoint E hrootInjective hrootOutside hrootCut

end Erdos547b.ZhaoLemma58CutForestReconstruction

#print axioms Erdos547b.ZhaoLemma58CutForestReconstruction.cutBranchGraphIso_nonroot
#print axioms Erdos547b.ZhaoLemma58CutForestReconstruction.treeCopyOfCertifiedMatchingFibersOfLE
#print axioms Erdos547b.ZhaoLemma58CutForestReconstruction.treeCopyOfCertifiedMatchingFibers
