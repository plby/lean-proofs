/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateCutAttachmentParity

/-!
# Marking the recorded Claim 6.16 cut parents

The recorded Zhao cut parents already form the finite set `partitionParents`.
Including that set among the optional hierarchy marks makes every component-
root attachment land at the root coordinate of the parent segment.  This is
the structural fact which lets the rich host use its existing root pairs;
no additional cross-pair assumption is introduced.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateCutParents

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616CoordinateCutAttachmentParity
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The literal recorded cut parents, under a Claim-6.16-facing name. -/
abbrev cutParentVertices
    (P : ZhaoForestPartition T globalRoot small) : Finset V :=
  partitionParents P

theorem card_cutParentVertices_le_numParts
    (P : ZhaoForestPartition T globalRoot small) :
    #(cutParentVertices P) ≤ P.numParts :=
  card_partitionParents_le_numParts P

/-- Every recorded cut parent has canonical local side zero in its branch
class, so the whole cut-parent set satisfies the optional-root parity
condition. -/
theorem cutParentVertices_optionalBranchRootParity
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small) :
    OptionalBranchRootParity P (cutParentVertices P) := by
  intro x hx j hclass
  rw [cutParentVertices, partitionParents] at hx
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
  exact cutParent_canonicalBranchSide_zero hT P q.1 q.2 j hclass

/-- Every non-global optional source vertex is represented by the root of a
unique marked hierarchy segment. -/
theorem exists_segmentRoot_of_mem_optional
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) {x : V} (hx : x ∈ optional)
    (hxGlobal : x ≠ globalRoot) :
    ∃ i : SegmentIndex hT P optional,
      toWholeHierarchyVertex T hT globalRoot
          (AllocationSpecial hT P optional) x =
        (AllocationHierarchy hT P optional).segmentRoot i := by
  classical
  let F := wholeBranchForest T hT globalRoot
  let rawSpecial := (zhaoMarkedVertices P optional).image
    (toWholeBranchForestVertex T hT globalRoot)
  have hxMarked : x ∈ zhaoMarkedVertices P optional := by
    rw [zhaoMarkedVertices_eq_allocationMarkedVertices P optional]
    exact optional_subset_allocationMarkedVertices P optional hx
  have hxImage : toWholeBranchForestVertex T hT globalRoot x ∈ rawSpecial :=
    Finset.mem_image.mpr ⟨x, hxMarked, rfl⟩
  cases hcoord : toWholeBranchForestVertex T hT globalRoot x with
  | inl q =>
      have hq : q = 0 := Subsingleton.elim _ _
      have hbad : x = globalRoot := by
        apply toWholeBranchForestVertex_injective T hT globalRoot
        rw [hcoord, hq, toWholeBranchForestVertex_root]
      exact False.elim (hxGlobal hbad)
  | inr z =>
      have hz : (Sum.inr z : F.Vertex) ∈ rawSpecial := by
        rw [hcoord] at hxImage
        exact hxImage
      obtain ⟨i, hi⟩ := unflatten_branchSpecial_is_segmentRoot
        F rawSpecial z hz
      refine ⟨i, ?_⟩
      change unflatten F (branchSpecial F rawSpecial)
          (toWholeBranchForestVertex T hT globalRoot x) = _
      rw [hcoord]
      exact hi

/-- If all recorded cut parents are optional marks, then the parent
coordinate of a component-root segment is literally the root coordinate of
its parent hierarchy segment. -/
theorem componentRoot_attachment_coordinate_eq_segmentRoot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hcut : cutParentVertices P ⊆ optional)
    (i k : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size k))
    (q : Fin P.numParts)
    (hi : segmentSourceClass hT P optional i = Sum.inl q)
    (hparent : (AllocationHierarchy hT P optional).parent i =
      Sum.inr ⟨k, a⟩) :
    a = (AllocationHierarchy hT P optional).segments.root k := by
  have hroot : SegmentRootOriginal hT P optional i = P.roots q := by
    apply (literalSourceClass_eq_inl_iff P _ q).mp
    exact hi
  have hq : q.val ≠ 0 := by
    intro hq0
    have hqeq : q = ⟨0, P.numParts_pos⟩ := Fin.ext hq0
    have hglobal : P.roots q = globalRoot := by
      rw [hqeq, P.first_root]
    exact segmentRootOriginal_ne_globalRoot hT P optional i
      (hroot.trans hglobal)
  have hparentValue :
      wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P optional) (Sum.inr ⟨k, a⟩) =
        P.parent q hq := by
    calc
      _ = SegmentParentOriginal hT P optional i := by
        exact congrArg
          (wholeHierarchyOriginalVertex T hT globalRoot
            (AllocationSpecial hT P optional)) hparent.symm
      _ = TreePartition.parent hT globalRoot
          (segmentRootOriginal_ne_globalRoot hT P optional i) :=
        segmentParentOriginal_eq_treeParent hT P optional i
      _ = P.parent q hq := by
        symm
        apply TreePartition.eq_parent_of_adj_of_dist_add_one hT globalRoot
        · simpa only [hroot] using (P.cut_adj q hq).symm
        · simpa only [hroot] using cutParent_dist_add_one hT P q hq
  have hparentMem : P.parent q hq ∈ cutParentVertices P := by
    rw [cutParentVertices, partitionParents]
    exact Finset.mem_image.mpr ⟨⟨q, hq⟩, Finset.mem_univ _, rfl⟩
  have hparentOptional : P.parent q hq ∈ optional := hcut hparentMem
  have hparentGlobal : P.parent q hq ≠ globalRoot := by
    intro hglobal
    have hparentCoordinate :
        (Sum.inr ⟨k, a⟩ : (AllocationHierarchy hT P optional).Vertex) =
          Sum.inl 0 := by
      apply wholeHierarchyOriginalVertex_injective hT
        (AllocationSpecial hT P optional)
      rw [hparentValue, hglobal, wholeHierarchyOriginal_inl_zero]
    cases hparentCoordinate
  obtain ⟨l, hl⟩ := exists_segmentRoot_of_mem_optional hT P optional
    hparentOptional hparentGlobal
  have hrootValue :
      wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P optional)
          ((AllocationHierarchy hT P optional).segmentRoot l) =
        P.parent q hq := by
    rw [← hl, wholeHierarchyOriginal_toWholeHierarchyVertex]
  have hcoordinate :
      (Sum.inr ⟨k, a⟩ : (AllocationHierarchy hT P optional).Vertex) =
        (AllocationHierarchy hT P optional).segmentRoot l := by
    apply wholeHierarchyOriginalVertex_injective hT
      (AllocationSpecial hT P optional)
    exact hparentValue.trans hrootValue.symm
  have hsigma :
      (⟨k, a⟩ : Σ j,
        Fin ((AllocationHierarchy hT P optional).segments.size j)) =
      ⟨l, (AllocationHierarchy hT P optional).segments.root l⟩ :=
    Sum.inr.inj hcoordinate
  have hkl : k = l := (Sigma.mk.inj_iff.mp hsigma).1
  subst l
  exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2

end Erdos547b.ZhaoClaim616CoordinateCutParents

#print axioms Erdos547b.ZhaoClaim616CoordinateCutParents.card_cutParentVertices_le_numParts
#print axioms Erdos547b.ZhaoClaim616CoordinateCutParents.cutParentVertices_optionalBranchRootParity
#print axioms Erdos547b.ZhaoClaim616CoordinateCutParents.componentRoot_attachment_coordinate_eq_segmentRoot
