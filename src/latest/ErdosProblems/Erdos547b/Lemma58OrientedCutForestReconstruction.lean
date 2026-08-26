/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58CutForestReconstruction
import ErdosProblems.Erdos547b.Claim616HierarchyClassification

/-!
# Orientation-sensitive reconstruction of Zhao's cut forest

The older cut-parent certificate removes, on every endpoint used by an
owner, the non-neighbours of every later root attached inside that owner.
That is stronger than the proof needs and is false at a zero-density unused
endpoint.  Here the bad set remembers the literal matching edge and oriented
side containing the deleted parent.  Thus a root is charged only against its
actual host target.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58OrientedCutForestReconstruction

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoLemma614Full
open Erdos547b.ZhaoLemma59FullOnline
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58CertifiedMatchingAssembly
open Erdos547b.ZhaoLemma58CutForestReconstruction

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Vertices of endpoint `(e,c)` which fail adjacency to a later root whose
literal non-root cut parent is embedded on that same edge and oriented side.
The owner parameter is retained because the certified local assembly is
owner-indexed. -/
def orientedCutParentBad
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 ≃ Fin 2)
    (e : Fin k) (q : Fin P.numParts) (c : Fin 2) : Finset B :=
  (endpoint e c).filter fun x ↦
    ∃ j : Fin P.numParts, ∃ hj : j.val ≠ 0,
      ∃ hnonroot : P.parent j hj ∉ partitionRoots P,
        let z := literalBranchCoordinate P (P.parent j hj) hnonroot
        (branchForest P).owner z.1 = q ∧
          assign z.1 = e ∧
          orient z.1
              ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
                ((branchForest P).branches.root z.1) z.2) = c ∧
          ¬ G.Adj (rootImage j) x

@[simp] theorem mem_orientedCutParentBad
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 ≃ Fin 2)
    (e : Fin k) (q : Fin P.numParts) (c : Fin 2) (x : B) :
    x ∈ orientedCutParentBad P G rootImage assign endpoint orient e q c ↔
      x ∈ endpoint e c ∧
      ∃ j : Fin P.numParts, ∃ hj : j.val ≠ 0,
        ∃ hnonroot : P.parent j hj ∉ partitionRoots P,
          let z := literalBranchCoordinate P (P.parent j hj) hnonroot
          (branchForest P).owner z.1 = q ∧
            assign z.1 = e ∧
            orient z.1
                ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
                  ((branchForest P).branches.root z.1) z.2) = c ∧
            ¬ G.Adj (rootImage j) x := by
  rw [orientedCutParentBad, Finset.mem_filter]

/-- A certified realization avoiding the orientation-sensitive bad sets
reconstructs every deleted cut edge. -/
noncomputable def treeCopyOfOrientedCertifiedMatchingFibersOfLE
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (hGle : Gpair ≤ Gtarget)
    {k : ℕ} (rootImage : Fin P.numParts → B)
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 ≃ Fin 2)
    (E : CertifiedRootAttachedBranchEmbedding (branchForest P) Gpair rootImage
      assign endpoint
      (fun e q c ↦ orientedCutParentBad P Gtarget rootImage assign endpoint
        orient e q c))
    (horient : E.orient = orient)
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
      literalBranchCoordinate P (P.parent j hj)
        (Finset.mem_sdiff.mp hparentNonroot).2
    have hzval : (partitionBranchEquivNonroots P z).1 = P.parent j hj :=
      partitionBranchEquivNonroots_literalBranchCoordinate P
        (P.parent j hj) (Finset.mem_sdiff.mp hparentNonroot).2
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
    have hbad : E.embedding.branchEmbedding.copy z.1 z.2 ∈
        orientedCutParentBad P Gtarget rootImage assign endpoint orient
          (assign z.1) ((branchForest P).owner z.1)
          (E.orient z.1
            ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
              ((branchForest P).branches.root z.1) z.2)) := by
      apply (mem_orientedCutParentBad P Gtarget rootImage assign endpoint
        orient _ _ _ _).2
      refine ⟨hmem, j, hj, (Finset.mem_sdiff.mp hparentNonroot).2, ?_⟩
      have ho := congrArg
        (fun O ↦ O z.1
          ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
            ((branchForest P).branches.root z.1) z.2)) horient
      exact ⟨rfl, rfl, ho.symm, hnotAdj⟩
    exact E.avoids z.1 z.2 hbad

end Erdos547b.ZhaoLemma58OrientedCutForestReconstruction

#print axioms Erdos547b.ZhaoLemma58OrientedCutForestReconstruction.treeCopyOfOrientedCertifiedMatchingFibersOfLE
