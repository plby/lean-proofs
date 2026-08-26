/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchyClassification

/-!
# Source attachments and endpoint sides for the Claim 6.16 hierarchy

This file records the source information needed by the rich hierarchical
host construction.  A segment of canonical Zhao branch class `j` is either
the first segment of that branch, attached to the owning component root, or
is attached to a coordinate of a strictly earlier segment of the same
canonical branch.  Everything is derived from the literal tree and the
segmentation; there is no host graph, copy, or candidate premise.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchyAttachments

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim68BranchGraphTransport
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoLemma59FullOnline
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma614HierarchicalFullTree
open Erdos547b.ZhaoSingleTreeOrderedForest

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Major Zhao component roots use tag `0`, minor component roots tag `1`.
This is source data, so it lives before the host-layout module that interprets
the tags as the two distinguished reservoirs. -/
def componentReservoirSide
    (P : ZhaoForestPartition T globalRoot small) (q : Fin P.numParts) : Fin 2 :=
  if T.dist globalRoot (P.roots q) % 2 = (majorParity P).val then 0 else 1

abbrev SegmentRootOriginal
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional) : V :=
  wholeHierarchyOriginalVertex T hT globalRoot
    (AllocationSpecial hT P optional)
    ((AllocationHierarchy hT P optional).segmentRoot i)

abbrev SegmentParentOriginal
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional) : V :=
  wholeHierarchyOriginalVertex T hT globalRoot
    (AllocationSpecial hT P optional)
    ((AllocationHierarchy hT P optional).parent i)

@[simp] theorem wholeHierarchyOriginal_inl_zero
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    wholeHierarchyOriginalVertex T hT globalRoot
        (AllocationSpecial hT P optional) (Sum.inl 0) = globalRoot := by
  have h := wholeHierarchyOriginal_toWholeHierarchyVertex T hT globalRoot
    (AllocationSpecial hT P optional) globalRoot
  simpa [toWholeHierarchyVertex, toWholeBranchForestVertex_root, unflatten] using h

theorem segmentRootOriginal_eq_wholeBranchLiteralVertex
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional) :
    SegmentRootOriginal hT P optional i =
      wholeBranchLiteralVertex hT
        (markEnum (wholeBranchForest T hT globalRoot)
          (AllocationSpecial hT P optional) i).1.1
        (markEnum (wholeBranchForest T hT globalRoot)
          (AllocationSpecial hT P optional) i).1.2 := by
  rw [SegmentRootOriginal, wholeHierarchyOriginalVertex,
    flatten_segmentRoot]
  rfl

theorem segmentRootOriginal_ne_globalRoot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional) :
    SegmentRootOriginal hT P optional i ≠ globalRoot := by
  rw [segmentRootOriginal_eq_wholeBranchLiteralVertex]
  exact wholeBranchLiteralVertex_ne_globalRoot hT _ _

/-- Forgetting the unique component coordinate reflects an edge of the
one-component ordered forest back to an edge of the literal tree. -/
theorem fromSingleCoordinate_map_adj
    (hT : T.IsTree)
    {x y : Σ i, Fin ((wholeOrderedTree T hT globalRoot).size i)}
    (hxy : (wholeOrderedTree T hT globalRoot).graph.Adj x y) :
    T.Adj (fromSingleCoordinate T hT globalRoot x)
      (fromSingleCoordinate T hT globalRoot y) := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  rcases (Erdos547b.RegularPair.OrderedRootedForest.graph_adj _ _).mp hxy with
    ⟨q, c, d, hc, hd, hcd⟩
  have hq : q = 0 := Subsingleton.elim _ _
  subst q
  have hca : c = a := by
    exact (eq_of_heq (Sigma.mk.inj_iff.mp hc).2).symm
  have hdb : d = b := by
    exact (eq_of_heq (Sigma.mk.inj_iff.mp hd).2).symm
  subst c
  subst d
  change T.Adj (vertexEquiv a) (vertexEquiv b)
  exact hcd

/-- The root of a canonical branch in the one-root decomposition is an
actual child of the global root. -/
theorem wholeBranchRoot_treeParent
    (hT : T.IsTree)
    (j : Fin (Fintype.card (ChildKey
      (wholeOrderedTree T hT globalRoot)))) :
    TreePartition.parent hT globalRoot
        (wholeBranchLiteralVertex_ne_globalRoot hT j
          ((wholeBranchForest T hT globalRoot).branches.root j)) =
      globalRoot := by
  let F := wholeBranchForest T hT globalRoot
  have hbranch : F.graph.Adj (Sum.inl (F.owner j))
      (Sum.inr (⟨j, F.branches.root j⟩ : BranchVertex F)) := ⟨rfl, rfl⟩
  have hordered :=
    (branchGraphIso (wholeOrderedTree T hT globalRoot)).toHom.map_rel hbranch
  have hadj : T.Adj globalRoot
      (wholeBranchLiteralVertex hT j (F.branches.root j)) := by
    have howner : F.owner j = 0 := Subsingleton.elim _ _
    have hmapped := fromSingleCoordinate_map_adj hT hordered
    have hleft : fromSingleCoordinate T hT globalRoot
        (flattenBranch (wholeOrderedTree T hT globalRoot)
          (Sum.inl (F.owner j))) = globalRoot := by
      rw [howner, flattenBranch_root]
      simp [fromSingleCoordinate, wholeOrderedTree, singleOrderedRootedTree,
        vertexEquiv]
    have hright : fromSingleCoordinate T hT globalRoot
        (flattenBranch (wholeOrderedTree T hT globalRoot)
          (Sum.inr (⟨j, F.branches.root j⟩ : BranchVertex F))) =
        wholeBranchLiteralVertex hT j (F.branches.root j) := by
      rfl
    change T.Adj
      (fromSingleCoordinate T hT globalRoot
        (flattenBranch (wholeOrderedTree T hT globalRoot)
          (Sum.inl (F.owner j))))
      (fromSingleCoordinate T hT globalRoot
        (flattenBranch (wholeOrderedTree T hT globalRoot)
          (Sum.inr (⟨j, F.branches.root j⟩ : BranchVertex F)))) at hmapped
    rw [hleft, hright] at hmapped
    exact hmapped
  symm
  apply TreePartition.eq_parent_of_adj_of_dist_add_one hT globalRoot
    (wholeBranchLiteralVertex_ne_globalRoot hT j (F.branches.root j))
  · exact hadj
  · have hdist : T.dist globalRoot
        (wholeBranchLiteralVertex hT j (F.branches.root j)) = 1 :=
      T.dist_eq_one_iff_adj.mpr hadj
    simpa only [SimpleGraph.dist_self, zero_add,
      wholeBranchLiteralVertex_eq_wholeBranchOriginal] using hdist.symm

/-- Every hierarchy attachment is literally the rooted-tree parent edge of
its segment root. -/
theorem segmentParentOriginal_eq_treeParent
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional) :
    SegmentParentOriginal hT P optional i =
      TreePartition.parent hT globalRoot
        (segmentRootOriginal_ne_globalRoot hT P optional i) := by
  let F := wholeBranchForest T hT globalRoot
  let special := AllocationSpecial hT P optional
  let q : BranchVertex F := (markEnum F special i).1
  by_cases hqroot : q.2 = F.branches.root q.1
  · have hqeq : q =
        (⟨q.1, F.branches.root q.1⟩ : BranchVertex F) := by
      refine Sigma.ext rfl ?_
      exact heq_of_eq hqroot
    have hi : i = markIndex F special
        (⟨q.1, F.branches.root q.1⟩ : BranchVertex F)
        (branchRoot_mem_marks F special q.1) := by
      apply (markEnum F special).injective
      apply Subtype.ext
      simpa only [markEnum_index] using hqeq
    rw [hi, SegmentParentOriginal,
      segmentParent_branchRoot F special q.1]
    have howner : F.owner q.1 = 0 := Subsingleton.elim _ _
    rw [howner]
    rw [wholeHierarchyOriginal_inl_zero]
    have hroot := wholeBranchRoot_treeParent hT q.1
    have hsegRoot : SegmentRootOriginal hT P optional
          (markIndex F special
            (⟨q.1, F.branches.root q.1⟩ : BranchVertex F)
            (branchRoot_mem_marks F special q.1)) =
        wholeBranchLiteralVertex hT q.1 (F.branches.root q.1) := by
      rw [segmentRootOriginal_eq_wholeBranchLiteralVertex]
      exact congrArg
        (fun z : BranchVertex F ↦ wholeBranchLiteralVertex hT z.1 z.2)
        (markEnum_index F special
          (⟨q.1, F.branches.root q.1⟩ : BranchVertex F)
          (branchRoot_mem_marks F special q.1))
    simpa only [hsegRoot] using hroot.symm
  · rw [SegmentParentOriginal, wholeHierarchyOriginalVertex,
      flatten_segmentParent_of_not_root F special i hqroot]
    have hsegRoot : SegmentRootOriginal hT P optional i =
        wholeBranchLiteralVertex hT q.1 q.2 := by
      rw [segmentRootOriginal_eq_wholeBranchLiteralVertex]
    change wholeBranchLiteralVertex hT q.1
        (TreePartition.parent (F.branches.isTree q.1)
          (F.branches.root q.1) hqroot) =
      TreePartition.parent hT globalRoot
        (segmentRootOriginal_ne_globalRoot hT P optional i)
    simpa only [hsegRoot] using
      (canonicalWholeBranchParentTransport hT q.1 q.2 hqroot)

/-- The root of a canonical Zhao root-deleted branch is an actual child of
the distinguished root of its cut component. -/
theorem actualBranchRoot_dist_add_one
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (j : BranchIndex P) :
    T.dist globalRoot (P.roots ((branchForest P).owner j)) + 1 =
      T.dist globalRoot (actualBranchRoot P j) := by
  have hlevel := actualBranchRoot_mem_levelOne P j
  obtain ⟨q, hqadj⟩ := (Finset.mem_filter.mp hlevel).2
  have hidx : q = (branchForest P).owner j := by
    have hcc := ConnectedComponent.connectedComponentMk_eq_of_adj hqadj
    have hcomponent : P.componentIndex (P.roots q) =
        P.componentIndex (actualBranchRoot P j) := by
      unfold ZhaoForestPartition.componentIndex
      rw [hcc]
    rw [componentIndex_roots, actualBranchRoot_eq_partitionBranchEquiv,
      partitionBranchEquivNonroots_component] at hcomponent
    exact hcomponent
  subst q
  rcases hT.dist_eq_dist_add_one_of_adj globalRoot hqadj.1 with hbad | hgood
  · let owner := (branchForest P).owner j
    by_cases howner0 : owner.val = 0
    · have hroot : P.roots owner = globalRoot := by
        have howner : owner = ⟨0, P.numParts_pos⟩ := Fin.ext howner0
        simpa [howner] using P.first_root
      rw [hroot] at hbad
      simp at hbad
    · have hparent : actualBranchRoot P j =
          TreePartition.parent hT globalRoot
            (cutRoot_ne_globalRoot hT P owner howner0) := by
        apply TreePartition.eq_parent_of_adj_of_dist_add_one hT globalRoot
        · exact hqadj.1.symm
        · exact hbad.symm
      have hrecorded := cutParent_eq_treeParent hT P owner howner0
      have hsame : actualBranchRoot P j = P.parent owner howner0 :=
        hparent.trans hrecorded.symm
      have hcomponentActual : P.componentIndex (actualBranchRoot P j) = owner := by
        rw [actualBranchRoot_eq_partitionBranchEquiv,
          partitionBranchEquivNonroots_component]
      have hcomponentParent := componentIndex_parent P owner howner0
      rw [hsame, hcomponentParent] at hcomponentActual
      have hearler := P.parent_earlier owner howner0
      rw [hcomponentActual] at hearler
      exact False.elim (Nat.lt_irrefl owner.val hearler)
  · exact hgood.symm

theorem actualBranchRoot_treeParent
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (j : BranchIndex P) :
    TreePartition.parent hT globalRoot (actualBranchRoot_ne_globalRoot P j) =
      P.roots ((branchForest P).owner j) := by
  symm
  apply TreePartition.eq_parent_of_adj_of_dist_add_one hT globalRoot
  · have hlevel := actualBranchRoot_mem_levelOne P j
    obtain ⟨q, hqadj⟩ := (Finset.mem_filter.mp hlevel).2
    have hidx : q = (branchForest P).owner j := by
      have hcc := ConnectedComponent.connectedComponentMk_eq_of_adj hqadj
      have hcomponent : P.componentIndex (P.roots q) =
          P.componentIndex (actualBranchRoot P j) := by
        unfold ZhaoForestPartition.componentIndex
        rw [hcc]
      rw [componentIndex_roots, actualBranchRoot_eq_partitionBranchEquiv,
        partitionBranchEquivNonroots_component] at hcomponent
      exact hcomponent
    simpa [hidx] using hqadj.1
  · exact actualBranchRoot_dist_add_one hT P j

/-- Exact source attachment alternative for a segment of canonical branch
class `j`.  In the second alternative the hierarchy coordinate of the
parent lies in a strictly earlier segment of the same class. -/
theorem segment_attachment_of_branch_class
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional)
    (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j) :
    (SegmentRootOriginal hT P optional i = actualBranchRoot P j ∧
      SegmentParentOriginal hT P optional i =
        P.roots ((branchForest P).owner j)) ∨
    ∃ k a,
      (AllocationHierarchy hT P optional).parent i = Sum.inr ⟨k, a⟩ ∧
      k.val < i.val ∧
      segmentSourceClass hT P optional k = Sum.inr j := by
  classical
  let H := AllocationHierarchy hT P optional
  let x := SegmentRootOriginal hT P optional i
  by_cases hx : x = actualBranchRoot P j
  · left
    change SegmentRootOriginal hT P optional i = actualBranchRoot P j at hx
    refine ⟨hx, ?_⟩
    have hp := segmentParentOriginal_eq_treeParent hT P optional i
    have ht := actualBranchRoot_treeParent hT P j
    have hadjActual : T.Adj (P.roots ((branchForest P).owner j))
        (actualBranchRoot P j) := by
      rw [← ht]
      exact TreePartition.parent_adj hT globalRoot
        (actualBranchRoot_ne_globalRoot P j)
    have hdistActual :
        T.dist globalRoot (P.roots ((branchForest P).owner j)) + 1 =
          T.dist globalRoot (actualBranchRoot P j) := by
      rw [← ht]
      exact TreePartition.parent_dist_add_one hT globalRoot
        (actualBranchRoot_ne_globalRoot P j)
    have hadjRoot : T.Adj (P.roots ((branchForest P).owner j))
        (SegmentRootOriginal hT P optional i) := by
      simpa only [hx] using hadjActual
    have hdistRoot :
        T.dist globalRoot (P.roots ((branchForest P).owner j)) + 1 =
          T.dist globalRoot (SegmentRootOriginal hT P optional i) := by
      simpa only [hx] using hdistActual
    exact hp.trans
      (TreePartition.eq_parent_of_adj_of_dist_add_one hT globalRoot
        (segmentRootOriginal_ne_globalRoot hT P optional i)
        hadjRoot hdistRoot).symm
  · right
    have hxNotRoot : x ∉ partitionRoots P := by
      intro hxRoot
      obtain ⟨q, -, hqx⟩ := Finset.mem_image.mp hxRoot
      have hinl : literalSourceClass P x = Sum.inl q := by
        have hqRoot : P.roots q ∈ partitionRoots P :=
          Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
        have hqClass : literalSourceClass P (P.roots q) = Sum.inl q := by
          rw [literalSourceClass_of_root P (P.roots q) hqRoot,
            componentIndex_roots]
        simpa only [hqx] using hqClass
      change literalSourceClass P x = Sum.inr j at hclass
      rw [hinl] at hclass
      cases hclass
    let p := TreePartition.parent hT globalRoot
      (segmentRootOriginal_ne_globalRoot hT P optional i)
    have hpCut : P.cutForest.Adj p x :=
      cutForest_adj_treeParent_of_nonroot hT P x
        (segmentRootOriginal_ne_globalRoot hT P optional i) hxNotRoot
    have hpNotRoot : p ∉ partitionRoots P := by
      intro hpRoot
      have hxNonroot : x ∈ partitionNonroots P :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxNotRoot⟩
      let z := (partitionBranchEquivNonroots P).symm ⟨x, hxNonroot⟩
      have hzRoot : z.2 = (branchForest P).branches.root z.1 :=
        branchCoordinate_eq_root_of_cutAdj_partitionRoot P hpRoot hxNonroot hpCut
      have hxActual : x = actualBranchRoot P z.1 := by
        rw [actualBranchRoot_eq_partitionBranchEquiv, ← hzRoot]
        exact (congrArg Subtype.val (Equiv.apply_symm_apply
          (partitionBranchEquivNonroots P) ⟨x, hxNonroot⟩)).symm
      have hzClass : literalSourceClass P x = Sum.inr z.1 := by
        rw [hxActual, actualBranchRoot_eq_partitionBranchEquiv,
          literalSourceClass_partitionBranchEquivNonroots]
      change literalSourceClass P x = Sum.inr j at hclass
      have hzj : z.1 = j := Sum.inr.inj (hzClass.symm.trans hclass)
      exact hx (hxActual.trans (congrArg (actualBranchRoot P) hzj))
    have hpNonroot : p ∈ partitionNonroots P :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpNotRoot⟩
    have hxNonroot : x ∈ partitionNonroots P :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxNotRoot⟩
    have hpClass : literalSourceClass P p = Sum.inr j := by
      have heq := literalSourceClass_eq_of_cutAdj_of_nonroots P
        hpNonroot hxNonroot hpCut
      change literalSourceClass P x = Sum.inr j at hclass
      exact heq.trans hclass
    cases hparent : H.parent i with
    | inl q =>
        have hpGlobal : p = globalRoot := by
          have hp := segmentParentOriginal_eq_treeParent hT P optional i
          change SegmentParentOriginal hT P optional i = p at hp
          have hsegParent : SegmentParentOriginal hT P optional i = globalRoot := by
            unfold SegmentParentOriginal
            rw [hparent]
            have hq : q = 0 := Subsingleton.elim _ _
            subst q
            exact wholeHierarchyOriginal_inl_zero hT P optional
          exact hp.symm.trans hsegParent
        apply False.elim
        apply hpNotRoot
        rw [hpGlobal]
        apply Finset.mem_image.mpr
        exact ⟨⟨0, P.numParts_pos⟩, Finset.mem_univ _, P.first_root⟩
    | inr z =>
        rcases z with ⟨k, a⟩
        refine ⟨k, a, rfl, H.parent_earlier i k a hparent, ?_⟩
        have hcoordClass := wholeSegment_sourceClass_eq_of_boundary hT P optional
          (canonicalWholeSourceBoundary hT P optional) k a
        change literalSourceClass P
            (wholeHierarchyOriginalVertex T hT globalRoot
              (AllocationSpecial hT P optional) (Sum.inr ⟨k, a⟩)) =
          segmentSourceClass hT P optional k at hcoordClass
        have hpOriginal : wholeHierarchyOriginalVertex T hT globalRoot
              (AllocationSpecial hT P optional) (Sum.inr ⟨k, a⟩) = p := by
          rw [← hparent]
          exact segmentParentOriginal_eq_treeParent hT P optional i
        rw [hpOriginal, hpClass] at hcoordClass
        exact hcoordClass.symm

/-- Exact classification of a segment attached directly to the unique
global hierarchy root.  Such a segment can be a marked Zhao component root;
otherwise it is the canonical root of a Zhao branch owned by component `0`.
The narrower assertion excluding the first alternative is false for a cut
edge joining the global root directly to a later component root. -/
theorem directSegment_sourceClass
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional)
    (hparent : (AllocationHierarchy hT P optional).parent i = Sum.inl 0) :
    (∃ q,
      segmentSourceClass hT P optional i = Sum.inl q ∧
      SegmentRootOriginal hT P optional i = P.roots q) ∨
    (∃ j,
      segmentSourceClass hT P optional i = Sum.inr j ∧
      (branchForest P).owner j = ⟨0, P.numParts_pos⟩ ∧
      SegmentRootOriginal hT P optional i = actualBranchRoot P j) := by
  classical
  have hparentOriginal : SegmentParentOriginal hT P optional i = globalRoot := by
    change wholeHierarchyOriginalVertex T hT globalRoot
        (AllocationSpecial hT P optional)
        ((AllocationHierarchy hT P optional).parent i) = globalRoot
    rw [hparent]
    exact wholeHierarchyOriginal_inl_zero hT P optional
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      left
      exact ⟨q, rfl,
        (literalSourceClass_eq_inl_iff P
          (SegmentRootOriginal hT P optional i) q).mp hclass⟩
  | inr j =>
      right
      rcases segment_attachment_of_branch_class hT P optional i j hclass with
          hfirst | hlater
      · refine ⟨j, rfl, ?_, hfirst.1⟩
        apply roots_injective P
        rw [P.first_root]
        exact hfirst.2.symm.trans hparentOriginal
      · obtain ⟨k, a, hparentLater, -, -⟩ := hlater
        rw [hparent] at hparentLater
        cases hparentLater

/-- A directly attached Zhao component-root segment lies in the reservoir
opposite to the global component root. -/
theorem directComponentReservoirSide_ne
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional)
    (q : Fin P.numParts)
    (hparent : (AllocationHierarchy hT P optional).parent i = Sum.inl 0)
    (hclass : segmentSourceClass hT P optional i = Sum.inl q) :
    componentReservoirSide P q ≠ componentReservoirSide P ⟨0, P.numParts_pos⟩ := by
  have hroot : SegmentRootOriginal hT P optional i = P.roots q :=
    (literalSourceClass_eq_inl_iff P
      (SegmentRootOriginal hT P optional i) q).mp hclass
  have hparentOriginal : SegmentParentOriginal hT P optional i = globalRoot := by
    change wholeHierarchyOriginalVertex T hT globalRoot
        (AllocationSpecial hT P optional)
        ((AllocationHierarchy hT P optional).parent i) = globalRoot
    rw [hparent]
    exact wholeHierarchyOriginal_inl_zero hT P optional
  have hadjRoot : T.Adj globalRoot (SegmentRootOriginal hT P optional i) := by
    have hadj' : T.Adj (SegmentParentOriginal hT P optional i)
        (SegmentRootOriginal hT P optional i) := by
      rw [segmentParentOriginal_eq_treeParent hT P optional i]
      exact TreePartition.parent_adj hT globalRoot
        (segmentRootOriginal_ne_globalRoot hT P optional i)
    simpa only [hparentOriginal] using hadj'
  have hadj : T.Adj globalRoot (P.roots q) := by
    simpa only [hroot] using hadjRoot
  have hparity := TreePartition.rootParity_ne_of_adj hT globalRoot hadj
  have hqParity : T.dist globalRoot (P.roots q) % 2 = 1 := by
    have hlt := Nat.mod_lt (T.dist globalRoot (P.roots q)) (by omega : 0 < 2)
    simp only [SimpleGraph.dist_self, Nat.zero_mod] at hparity
    omega
  generalize hm : majorParity P = m
  fin_cases m <;>
    simp [componentReservoirSide, hm, hqParity, P.first_root]

/-- Consumer-facing trichotomy for the branch alternative of
`directSegment_sourceClass`. -/
theorem branchClass_mem_selected_or_residual_or_minor
    {target slack : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) :
    j ∈ S.selected ∨ j ∈ majorResidualBranches P S ∨ j ∈ minorBranches P := by
  have hj : j ∈ S.selected ∪ majorResidualBranches P S ∪ minorBranches P := by
    rw [selected_union_residual_union_minor P S]
    exact Finset.mem_univ _
  rcases Finset.mem_union.mp hj with hjMajor | hjMinor
  · rcases Finset.mem_union.mp hjMajor with hjSelected | hjResidual
    · exact Or.inl hjSelected
    · exact Or.inr (Or.inl hjResidual)
  · exact Or.inr (Or.inr hjMinor)

/-- A branch-class segment root is either the canonical root of that Zhao
branch, or one of the genuinely optional marks. -/
theorem segmentRoot_eq_actualBranchRoot_or_mem_optional
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional)
    (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j) :
    SegmentRootOriginal hT P optional i = actualBranchRoot P j ∨
      SegmentRootOriginal hT P optional i ∈ optional := by
  classical
  let F := wholeBranchForest T hT globalRoot
  let special := AllocationSpecial hT P optional
  let q : BranchVertex F := (markEnum F special i).1
  by_cases hx : SegmentRootOriginal hT P optional i = actualBranchRoot P j
  · exact Or.inl hx
  · right
    have hqSpecial : q ∈ special := by
      rcases Finset.mem_union.mp (markEnum F special i).2 with hqRoot | hqSpecial
      · obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hqRoot
        have hqeq : q = (⟨l, F.branches.root l⟩ : BranchVertex F) := hl.symm
        have hi : i = markIndex F special
            (⟨l, F.branches.root l⟩ : BranchVertex F)
            (branchRoot_mem_marks F special l) := by
          simpa only [q, hqeq] using (markIndex_enum F special i).symm
        obtain ⟨k, a, hparent, -, -⟩ :=
          (segment_attachment_of_branch_class hT P optional i j hclass).resolve_left
            (fun hfirst ↦ hx hfirst.1)
        rw [hi, segmentParent_branchRoot F special l] at hparent
        cases hparent
      · exact hqSpecial
    have hqImage : (Sum.inr q : F.Vertex) ∈
        (zhaoMarkedVertices P optional).image
          (toWholeBranchForestVertex T hT globalRoot) := by
      exact (mem_branchSpecial F
        ((zhaoMarkedVertices P optional).image
          (toWholeBranchForestVertex T hT globalRoot)) q).mp hqSpecial
    obtain ⟨x, hxMarked, hxCoordinate⟩ := Finset.mem_image.mp hqImage
    have hxRoot : x = SegmentRootOriginal hT P optional i := by
      apply toWholeBranchForestVertex_injective T hT globalRoot
      rw [hxCoordinate, segmentRootOriginal_eq_wholeBranchLiteralVertex,
        toWholeBranchForestVertex_wholeBranchLiteralVertex]
    subst x
    rw [zhaoMarkedVertices_eq_allocationMarkedVertices,
      allocationMarkedVertices] at hxMarked
    rcases Finset.mem_union.mp hxMarked with hxPartitionRoot | hxRest
    · have hinl := literalSourceClass_of_root P
        (SegmentRootOriginal hT P optional i) hxPartitionRoot
      change literalSourceClass P
          (SegmentRootOriginal hT P optional i) = Sum.inr j at hclass
      rw [hinl] at hclass
      cases hclass
    · rcases Finset.mem_union.mp hxRest with hxActual | hxOptional
      · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hxActual
        have hkClass : literalSourceClass P
            (SegmentRootOriginal hT P optional i) = Sum.inr k := by
          rw [← hk, actualBranchRoot_eq_partitionBranchEquiv,
            literalSourceClass_partitionBranchEquivNonroots]
        change literalSourceClass P
            (SegmentRootOriginal hT P optional i) = Sum.inr j at hclass
        have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hclass)
        exact False.elim
          (hx (hk.symm.trans (congrArg (actualBranchRoot P) hkj)))
      · exact hxOptional

/-- Matching-endpoint parity relative to the canonical root of Zhao branch
`j`.  Consumers may orient the matching edge once per branch and use this
value for every segment coordinate inherited from that branch. -/
def canonicalBranchSide
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P)
    (x : V) : Fin 2 :=
  ⟨T.dist (actualBranchRoot P j) x % 2, Nat.mod_lt _ (by omega)⟩

def segmentEndpointSide
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional)
    (j : BranchIndex P)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) : Fin 2 :=
  canonicalBranchSide P j
    (wholeHierarchyOriginalVertex T hT globalRoot
      (AllocationSpecial hT P optional) (Sum.inr ⟨i, a⟩))

/-- Source-only parity condition on the genuinely optional hierarchy
roots. -/
def OptionalBranchRootParity
    (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) : Prop :=
  ∀ x ∈ optional, ∀ j,
    literalSourceClass P x = Sum.inr j → canonicalBranchSide P j x = 0

@[simp] theorem canonicalBranchSide_root
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P) :
    canonicalBranchSide P j (actualBranchRoot P j) = 0 := by
  apply Fin.ext
  simp [canonicalBranchSide]

/-- Canonical branch roots have side zero, and every other branch-class
segment root inherits side zero from the optional-set parity condition. -/
theorem segmentRoot_side_zero_of_optionalParity
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (i : SegmentIndex hT P optional) (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j) :
    canonicalBranchSide P j (SegmentRootOriginal hT P optional i) = 0 := by
  rcases segmentRoot_eq_actualBranchRoot_or_mem_optional hT P optional i j hclass with
      hroot | hoptional
  · rw [hroot]
    exact canonicalBranchSide_root P j
  · exact hparity (SegmentRootOriginal hT P optional i) hoptional j hclass

theorem segmentEndpointSide_root_zero_of_optionalParity
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (i : SegmentIndex hT P optional) (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j) :
    segmentEndpointSide hT P optional i j
      ((AllocationHierarchy hT P optional).segments.root i) = 0 := by
  change canonicalBranchSide P j (SegmentRootOriginal hT P optional i) = 0
  exact segmentRoot_side_zero_of_optionalParity hT P optional hparity i j hclass

/-- Adjacent literal source vertices occupy opposite endpoints of the
oriented matching pair. -/
theorem canonicalBranchSide_ne_of_adj
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (j : BranchIndex P) {x y : V} (hxy : T.Adj x y) :
    canonicalBranchSide P j x ≠ canonicalBranchSide P j y := by
  intro heq
  have hval := congrArg Fin.val heq
  change T.dist (actualBranchRoot P j) x % 2 =
    T.dist (actualBranchRoot P j) y % 2 at hval
  exact (TreePartition.rootParity_ne_of_adj hT (actualBranchRoot P j) hxy) hval

/-- The attachment endpoint of every branch segment has the opposite side
from the segment root. -/
theorem segmentParent_side_ne_segmentRoot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional)
    (j : BranchIndex P) :
    canonicalBranchSide P j (SegmentParentOriginal hT P optional i) ≠
      canonicalBranchSide P j (SegmentRootOriginal hT P optional i) := by
  rw [segmentParentOriginal_eq_treeParent hT P optional i]
  exact canonicalBranchSide_ne_of_adj hT P j
    (TreePartition.parent_adj hT globalRoot
      (segmentRootOriginal_ne_globalRoot hT P optional i))

theorem segmentParent_side_one_of_optionalParity
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (i : SegmentIndex hT P optional) (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j) :
    canonicalBranchSide P j (SegmentParentOriginal hT P optional i) = 1 := by
  have hne := segmentParent_side_ne_segmentRoot hT P optional i j
  have hzero := segmentRoot_side_zero_of_optionalParity
    hT P optional hparity i j hclass
  rw [hzero] at hne
  apply Fin.ext
  have hlt := (canonicalBranchSide P j
    (SegmentParentOriginal hT P optional i)).isLt
  have hnonzero : (canonicalBranchSide P j
      (SegmentParentOriginal hT P optional i)).val ≠ 0 := by
    intro hval
    apply hne
    apply Fin.ext
    simpa using hval
  omega

end Erdos547b.ZhaoClaim616HierarchyAttachments

#print axioms Erdos547b.ZhaoClaim616HierarchyAttachments.segment_attachment_of_branch_class
#print axioms Erdos547b.ZhaoClaim616HierarchyAttachments.canonicalBranchSide_ne_of_adj
