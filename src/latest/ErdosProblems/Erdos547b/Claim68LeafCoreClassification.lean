/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68HierarchicalLeaves
import ErdosProblems.Erdos547b.Claim616HierarchyClassification

/-!
# Canonical Zhao classes on the Claim 6.8 leaf-deleted core

Deleting the original Level-1 leaves must not erase the source boundary
used by Lemma 6.5.  The hierarchy in this file therefore marks every
surviving vertex of `allocationMarkedVertices P ∅`: the Zhao component
roots and the roots of the canonical root-deleted branches.  The resulting
segments do not mix canonical Zhao source classes.

All statements are source-side.  In particular, no host graph, copy, or
embedding implication occurs in this module.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim68LeafCoreClassification

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ConcreteLeaves
open Erdos547b.ZhaoClaim68BranchGraphTransport
open Erdos547b.ZhaoClaim68HierarchicalLeaves
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The original Zhao allocation boundaries which survive deletion of the
literal Claim-6.8 leaf set. -/
def leafDeletedAllocationMarked
    (P : ZhaoForestPartition T globalRoot small) :
    Finset (LeafDeletedVertex P) :=
  leafCoreMarkedVertices P

@[simp] theorem mem_leafDeletedAllocationMarked
    (P : ZhaoForestPartition T globalRoot small) (x : LeafDeletedVertex P) :
    x ∈ leafDeletedAllocationMarked P ↔
      x.1 ∈ allocationMarkedVertices P ∅ := by
  simp [leafDeletedAllocationMarked]

/-- All leaf parents used by the final Hall step remain among the stronger
allocation marks. -/
theorem leafDeletedPartitionRoots_subset_allocationMarked
    (P : ZhaoForestPartition T globalRoot small) :
    leafDeletedPartitionRoots P ⊆ leafDeletedAllocationMarked P := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_leafDeletedAllocationMarked P _).2
  apply partitionRoots_subset_allocationMarkedVertices P ∅
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The source-faithful hierarchy of the leaf-deleted core. -/
abbrev leafAllocationSpecial
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) :=
  leafCoreSpecial P hT

abbrev leafAllocationHierarchy
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) :=
  leafCoreHierarchy P hT

abbrev LeafSegmentIndex
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) :=
  Fin #(marks
    (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
      (leafDeletedGlobalRoot P))
    (leafAllocationSpecial P hT))

/-- The canonical source class of a surviving literal vertex. -/
def leafLiteralSourceClass
    (P : ZhaoForestPartition T globalRoot small) (x : LeafDeletedVertex P) :
    CanonicalSourceClass P :=
  literalSourceClass P x.1

/-- The canonical Zhao source class carried by a leaf-core segment. -/
def leafSegmentSourceClass
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (i : LeafSegmentIndex P hT) : CanonicalSourceClass P :=
  leafLiteralSourceClass P
    (wholeHierarchyOriginalVertex (leafDeletedCore P)
      (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
      (leafAllocationSpecial P hT)
      ((leafAllocationHierarchy P hT).segmentRoot i))

/-- Distances in the connected leaf-deleted induced subtree agree with
distances in the original tree. -/
theorem leafDeletedCore_dist_eq
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (x y : LeafDeletedVertex P) :
    (leafDeletedCore P).dist x y = T.dist x.1 y.1 := by
  exact induce_dist_eq_of_tree_of_connected hT _
    (leafDeletedCore_isTree P hT).connected x y

/-- Rooted parenthood is unchanged by deleting the original Level-1 leaves.
This is the key transport needed to reuse the original Zhao class boundary. -/
theorem leafDeleted_parent_val
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (x : LeafDeletedVertex P) (hx : x ≠ leafDeletedGlobalRoot P) :
    (TreePartition.parent (leafDeletedCore_isTree P hT)
        (leafDeletedGlobalRoot P) hx).1 =
      TreePartition.parent hT globalRoot (by
        intro h
        apply hx
        apply Subtype.ext
        exact h) := by
  apply TreePartition.eq_parent_of_adj_of_dist_add_one hT globalRoot
  · exact (TreePartition.parent_adj (leafDeletedCore_isTree P hT)
      (leafDeletedGlobalRoot P) hx)
  · have hdist := TreePartition.parent_dist_add_one
      (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P) hx
    rw [leafDeletedCore_dist_eq P hT,
      leafDeletedCore_dist_eq P hT] at hdist
    exact hdist

/-- Canonical branch coordinates of the leaf core, labelled by the original
Zhao source class. -/
def leafWholeBranchSourceClass
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (j : Fin (Fintype.card (ChildKey
      (wholeOrderedTree (leafDeletedCore P) (leafDeletedCore_isTree P hT)
        (leafDeletedGlobalRoot P)))))
    (a : Fin ((wholeBranchForest (leafDeletedCore P)
      (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)).branches.size j)) :
    CanonicalSourceClass P :=
  leafLiteralSourceClass P
    (wholeBranchLiteralVertex (T := leafDeletedCore P)
      (globalRoot := leafDeletedGlobalRoot P) (leafDeletedCore_isTree P hT) j a)

abbrev LeafWholeSourceBoundary
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) : Prop :=
  let F := wholeBranchForest (leafDeletedCore P)
    (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
  ∀ j a (haRoot : a ≠ F.branches.root j),
    leafWholeBranchSourceClass P hT j
        (TreePartition.parent (F.branches.isTree j)
          (F.branches.root j) haRoot) ≠
      leafWholeBranchSourceClass P hT j a →
    (⟨j, a⟩ : BranchVertex F) ∈
      marks F (leafAllocationSpecial P hT)

/-- Every original source-class change remains a hierarchy cut after leaf
deletion. -/
theorem canonicalLeafWholeSourceBoundary
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) :
    LeafWholeSourceBoundary P hT := by
  classical
  let core := leafDeletedCore P
  let coreTree := leafDeletedCore_isTree P hT
  let coreRoot := leafDeletedGlobalRoot P
  let F := wholeBranchForest core coreTree coreRoot
  intro j a haRoot hchange
  let x : LeafDeletedVertex P :=
    wholeBranchLiteralVertex (T := core) (globalRoot := coreRoot)
      coreTree j a
  have hxRoot : x ≠ coreRoot :=
    wholeBranchLiteralVertex_ne_globalRoot
      (T := core) (globalRoot := coreRoot) coreTree j a
  have hlocalParent := canonicalWholeBranchParentTransport
    (T := core) (globalRoot := coreRoot) coreTree j a haRoot
  have hchangeOriginal :
      literalSourceClass P
          (TreePartition.parent hT globalRoot (by
            intro hx
            apply hxRoot
            apply Subtype.ext
            exact hx)) ≠
        literalSourceClass P x.1 := by
    simpa only [leafWholeBranchSourceClass, leafLiteralSourceClass,
      hlocalParent, leafDeleted_parent_val P hT x hxRoot] using hchange
  have hxMarked : x.1 ∈ allocationMarkedVertices P ∅ := by
    rw [← zhaoMarkedVertices_eq_allocationMarkedVertices P ∅]
    exact literalSourceClass_change_at_markedVertex hT P ∅ x.1
      (by
        intro hx
        apply hxRoot
        apply Subtype.ext
        exact hx) hchangeOriginal
  apply special_subset_marks
  apply (mem_branchSpecial F
    ((leafDeletedAllocationMarked P).image
      (toWholeBranchForestVertex core coreTree coreRoot)) ⟨j, a⟩).2
  apply Finset.mem_image.mpr
  refine ⟨x, ?_, ?_⟩
  · exact (mem_leafDeletedAllocationMarked P x).2 hxMarked
  · exact toWholeBranchForestVertex_wholeBranchLiteralVertex
      (T := core) (globalRoot := coreRoot) coreTree j a

/-- No leaf-core hierarchy segment crosses an original Zhao source-class
boundary. -/
theorem leafWholeSegment_sourceClass_eq
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (i : LeafSegmentIndex P hT)
    (a : Fin ((leafAllocationHierarchy P hT).segments.size i)) :
    leafLiteralSourceClass P
        (wholeHierarchyOriginalVertex (leafDeletedCore P)
          (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
          (leafAllocationSpecial P hT) (Sum.inr ⟨i, a⟩)) =
      leafSegmentSourceClass P hT i := by
  let core := leafDeletedCore P
  let coreTree := leafDeletedCore_isTree P hT
  let coreRoot := leafDeletedGlobalRoot P
  let F := wholeBranchForest core coreTree coreRoot
  let special := leafAllocationSpecial P hT
  let q : BranchVertex F := (markEnum F special i).1
  change leafWholeBranchSourceClass P hT q.1
      (fiberEquiv F special i a).1 =
    leafWholeBranchSourceClass P hT q.1 q.2
  exact label_eq_mark_of_mem_fiber F special
    (leafWholeBranchSourceClass P hT)
    (canonicalLeafWholeSourceBoundary P hT) q
    (fiberEquiv F special i a).1 (fiberEquiv F special i a).2

/-! ## The four source classes on the leaf core -/

variable {target slack : ℕ}

def leafRootSegments
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) :
    Finset (LeafSegmentIndex P hT) :=
  Finset.univ.filter fun i ↦
    match leafSegmentSourceClass P hT i with
    | Sum.inl _ => True
    | Sum.inr _ => False

def leafF0Segments
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Finset (LeafSegmentIndex P hT) :=
  Finset.univ.filter fun i ↦
    match leafSegmentSourceClass P hT i with
    | Sum.inl _ => False
    | Sum.inr j => j ∈ S.selected

def leafF1Segments
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Finset (LeafSegmentIndex P hT) :=
  Finset.univ.filter fun i ↦
    match leafSegmentSourceClass P hT i with
    | Sum.inl _ => False
    | Sum.inr j => j ∈ majorResidualBranches P S

def leafFbSegments
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) :
    Finset (LeafSegmentIndex P hT) :=
  Finset.univ.filter fun i ↦
    match leafSegmentSourceClass P hT i with
    | Sum.inl _ => False
    | Sum.inr j => j ∈ minorBranches P

@[simp] theorem mem_leafRootSegments_iff
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (i : LeafSegmentIndex P hT) :
    i ∈ leafRootSegments P hT ↔
      ∃ q, leafSegmentSourceClass P hT i = Sum.inl q := by
  cases h : leafSegmentSourceClass P hT i with
  | inl q => simp [leafRootSegments, h]
  | inr j => simp [leafRootSegments, h]

@[simp] theorem mem_leafF0Segments_iff
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i : LeafSegmentIndex P hT) :
    i ∈ leafF0Segments P hT S ↔
      ∃ j ∈ S.selected,
        leafSegmentSourceClass P hT i = Sum.inr j := by
  cases h : leafSegmentSourceClass P hT i with
  | inl q => simp [leafF0Segments, h]
  | inr j => simp [leafF0Segments, h]

@[simp] theorem mem_leafF1Segments_iff
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i : LeafSegmentIndex P hT) :
    i ∈ leafF1Segments P hT S ↔
      ∃ j ∈ majorResidualBranches P S,
        leafSegmentSourceClass P hT i = Sum.inr j := by
  cases h : leafSegmentSourceClass P hT i with
  | inl q => simp [leafF1Segments, h]
  | inr j => simp [leafF1Segments, h]

@[simp] theorem mem_leafFbSegments_iff
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (i : LeafSegmentIndex P hT) :
    i ∈ leafFbSegments P hT ↔
      ∃ j ∈ minorBranches P,
        leafSegmentSourceClass P hT i = Sum.inr j := by
  cases h : leafSegmentSourceClass P hT i with
  | inl q => simp [leafFbSegments, h]
  | inr j => simp [leafFbSegments, h]

/-- The source classes remain exhaustive after literal leaf deletion. -/
theorem leafSegmentClass_cover
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    leafRootSegments P hT ∪
        (leafF0Segments P hT S ∪
          (leafF1Segments P hT S ∪ leafFbSegments P hT)) =
      Finset.univ := by
  ext i
  cases hclass : leafSegmentSourceClass P hT i with
  | inl q =>
      simp [leafRootSegments, leafF0Segments, leafF1Segments,
        leafFbSegments, hclass]
  | inr j =>
      have hj : j ∈ S.selected ∪ majorResidualBranches P S ∪
          minorBranches P := by
        rw [selected_union_residual_union_minor P S]
        exact Finset.mem_univ j
      simp only [Finset.mem_union] at hj
      rcases hj with (hj | hj) | hj
      · simp [leafRootSegments, leafF0Segments, leafF1Segments,
          leafFbSegments, hclass, hj]
      · simp [leafRootSegments, leafF0Segments, leafF1Segments,
          leafFbSegments, hclass, hj]
      · simp [leafRootSegments, leafF0Segments, leafF1Segments,
          leafFbSegments, hclass, hj]

/-- Component-root classes still consist of a single hierarchy vertex. -/
theorem leafRootSegment_size_eq_one
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (i : LeafSegmentIndex P hT) (hi : i ∈ leafRootSegments P hT) :
    (leafAllocationHierarchy P hT).segments.size i = 1 := by
  obtain ⟨q, hclass⟩ := (mem_leafRootSegments_iff P hT i).mp hi
  have hroot : ∀ a : Fin ((leafAllocationHierarchy P hT).segments.size i),
      (wholeHierarchyOriginalVertex (leafDeletedCore P)
          (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
          (leafAllocationSpecial P hT) (Sum.inr ⟨i, a⟩)).1 =
        P.roots q := by
    intro a
    apply (literalSourceClass_eq_inl_iff P _ q).mp
    exact (leafWholeSegment_sourceClass_eq P hT i a).trans hclass
  let f : Fin ((leafAllocationHierarchy P hT).segments.size i) → Unit :=
    fun _ ↦ ()
  have hf : Function.Injective f := by
    intro a b _
    have hsource :
        wholeHierarchyOriginalVertex (leafDeletedCore P)
            (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
            (leafAllocationSpecial P hT) (Sum.inr ⟨i, a⟩) =
          wholeHierarchyOriginalVertex (leafDeletedCore P)
            (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
            (leafAllocationSpecial P hT) (Sum.inr ⟨i, b⟩) := by
      apply Subtype.ext
      rw [hroot a, hroot b]
    have hver :
        (Sum.inr (⟨i, a⟩ : Σ k,
          Fin ((leafAllocationHierarchy P hT).segments.size k)) :
            (leafAllocationHierarchy P hT).Vertex) =
        Sum.inr (⟨i, b⟩ : Σ k,
          Fin ((leafAllocationHierarchy P hT).segments.size k)) := by
      apply wholeHierarchyOriginalVertex_injective
        (T := leafDeletedCore P) (globalRoot := leafDeletedGlobalRoot P)
        (leafDeletedCore_isTree P hT) (leafAllocationSpecial P hT)
      exact hsource
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj hver)).2
  have hle := Fintype.card_le_of_injective f hf
  have hpos := segmented_size_pos
    (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
      (leafDeletedGlobalRoot P)) (leafAllocationSpecial P hT) i
  simpa only [Fintype.card_fin, Fintype.card_unit] at hle
  omega

/-- Deleting leaves cannot make a segment of branch class `j` larger than
the original canonical branch `j`. -/
theorem leafSegment_size_le_sourceBranch
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (i : LeafSegmentIndex P hT) (j : BranchIndex P)
    (hclass : leafSegmentSourceClass P hT i = Sum.inr j) :
    (leafAllocationHierarchy P hT).segments.size i ≤
      (branchForest P).branches.size j := by
  classical
  let source : Fin ((leafAllocationHierarchy P hT).segments.size i) →
      LeafDeletedVertex P := fun a ↦
    wholeHierarchyOriginalVertex (leafDeletedCore P)
      (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
      (leafAllocationSpecial P hT) (Sum.inr ⟨i, a⟩)
  have hsourceClass : ∀ a,
      literalSourceClass P (source a).1 = Sum.inr j := by
    intro a
    exact (leafWholeSegment_sourceClass_eq P hT i a).trans hclass
  have hsourceNonroot : ∀ a, (source a).1 ∉ partitionRoots P := by
    intro a ha
    have hinl := literalSourceClass_of_root P (source a).1 ha
    rw [hsourceClass a] at hinl
    cases hinl
  have hindex : ∀ a,
      (literalBranchCoordinate P (source a).1 (hsourceNonroot a)).1 = j := by
    intro a
    have hcoord := literalSourceClass_eq_inr_literalBranchCoordinate P
      (source a).1 (hsourceNonroot a)
    exact Sum.inr.inj (hcoord.symm.trans (hsourceClass a))
  let f : Fin ((leafAllocationHierarchy P hT).segments.size i) →
      Fin ((branchForest P).branches.size j) := fun a ↦
    Fin.cast (by rw [hindex a])
      (literalBranchCoordinate P (source a).1 (hsourceNonroot a)).2
  have hf : Function.Injective f := by
    intro a b hab
    have hcoord :
        literalBranchCoordinate P (source a).1 (hsourceNonroot a) =
          literalBranchCoordinate P (source b).1 (hsourceNonroot b) := by
      apply Sigma.ext
      · rw [hindex a, hindex b]
      · have hval := congrArg Fin.val hab
        exact Fin.eq_of_val_eq hval
    have hvalue : (source a).1 = (source b).1 := by
      rw [← partitionBranchEquivNonroots_literalBranchCoordinate P
          (source a).1 (hsourceNonroot a),
        ← partitionBranchEquivNonroots_literalBranchCoordinate P
          (source b).1 (hsourceNonroot b), hcoord]
    have hsource : source a = source b := Subtype.ext hvalue
    have hver :
        (Sum.inr (⟨i, a⟩ : Σ k,
          Fin ((leafAllocationHierarchy P hT).segments.size k)) :
            (leafAllocationHierarchy P hT).Vertex) =
        Sum.inr (⟨i, b⟩ : Σ k,
          Fin ((leafAllocationHierarchy P hT).segments.size k)) := by
      apply wholeHierarchyOriginalVertex_injective
        (T := leafDeletedCore P) (globalRoot := leafDeletedGlobalRoot P)
        (leafDeletedCore_isTree P hT) (leafAllocationSpecial P hT)
      exact hsource
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj hver)).2
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem leafF0_segment_size_le_small
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i : LeafSegmentIndex P hT) (hi : i ∈ leafF0Segments P hT S) :
    (leafAllocationHierarchy P hT).segments.size i ≤ small := by
  obtain ⟨j, -, hj⟩ := (mem_leafF0Segments_iff P hT S i).mp hi
  exact (leafSegment_size_le_sourceBranch P hT i j hj).trans
    (canonical_branch_size_le_small P j)

theorem leafF1_segment_size_le_small
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i : LeafSegmentIndex P hT) (hi : i ∈ leafF1Segments P hT S) :
    (leafAllocationHierarchy P hT).segments.size i ≤ small := by
  obtain ⟨j, -, hj⟩ := (mem_leafF1Segments_iff P hT S i).mp hi
  exact (leafSegment_size_le_sourceBranch P hT i j hj).trans
    (canonical_branch_size_le_small P j)

theorem leafFb_segment_size_le_small
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (i : LeafSegmentIndex P hT) (hi : i ∈ leafFbSegments P hT) :
    (leafAllocationHierarchy P hT).segments.size i ≤ small := by
  obtain ⟨j, -, hj⟩ := (mem_leafFbSegments_iff P hT i).mp hi
  exact (leafSegment_size_le_sourceBranch P hT i j hj).trans
    (canonical_branch_size_le_small P j)

/-! ## Aggregate injection back into original branch bins -/

abbrev LeafSegmentMassCoordinate
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (I : Finset (LeafSegmentIndex P hT)) :=
  Σ i : {i // i ∈ I},
    Fin ((leafAllocationHierarchy P hT).segments.size i.1)

/-- Filtered leaf-core segment mass injects into the corresponding original
canonical branches. -/
theorem sum_leafSegmentSize_le_branchMass_of_class
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (I : Finset (LeafSegmentIndex P hT))
    (A : Finset (BranchIndex P))
    (hclass : ∀ i, i ∈ I →
      ∀ a : Fin ((leafAllocationHierarchy P hT).segments.size i),
        ∃ j ∈ A,
          literalSourceClass P
              (wholeHierarchyOriginalVertex (leafDeletedCore P)
                (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
                (leafAllocationSpecial P hT) (Sum.inr ⟨i, a⟩)).1 =
            Sum.inr j) :
    (∑ i ∈ I, (leafAllocationHierarchy P hT).segments.size i) ≤
      ∑ j ∈ A, (branchForest P).branches.size j := by
  classical
  let sourceVertex : LeafSegmentMassCoordinate P hT I → V := fun z ↦
    (wholeHierarchyOriginalVertex (leafDeletedCore P)
      (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
      (leafAllocationSpecial P hT) (Sum.inr ⟨z.1.1, z.2⟩)).1
  have sourceClass : ∀ z : LeafSegmentMassCoordinate P hT I,
      ∃ j ∈ A, literalSourceClass P (sourceVertex z) = Sum.inr j := by
    intro z
    exact hclass z.1.1 z.1.2 z.2
  have sourceNonroot : ∀ z : LeafSegmentMassCoordinate P hT I,
      sourceVertex z ∉ partitionRoots P := by
    intro z hz
    obtain ⟨j, -, hj⟩ := sourceClass z
    rw [literalSourceClass_of_root P (sourceVertex z) hz] at hj
    cases hj
  have coordinateMem : ∀ z : LeafSegmentMassCoordinate P hT I,
      (literalBranchCoordinate P (sourceVertex z) (sourceNonroot z)).1 ∈ A := by
    intro z
    obtain ⟨j, hjA, hj⟩ := sourceClass z
    have hcoord := literalSourceClass_eq_inr_literalBranchCoordinate P
      (sourceVertex z) (sourceNonroot z)
    have heq :
        (literalBranchCoordinate P (sourceVertex z) (sourceNonroot z)).1 = j :=
      Sum.inr.inj (hcoord.symm.trans hj)
    simpa [heq] using hjA
  let f : LeafSegmentMassCoordinate P hT I → BranchMassCoordinate P A :=
    fun z ↦ branchCoordinateIn P A (sourceVertex z)
      (sourceNonroot z) (coordinateMem z)
  let decode : BranchMassCoordinate P A → V := fun z ↦
    (partitionBranchEquivNonroots P
      (⟨z.1.1, z.2⟩ : Σ j, Fin ((branchForest P).branches.size j))).1
  have hdecode : ∀ z : LeafSegmentMassCoordinate P hT I,
      decode (f z) = sourceVertex z := by
    intro z
    exact decode_branchCoordinateIn P A (sourceVertex z)
      (sourceNonroot z) (coordinateMem z)
  have hf : Function.Injective f := by
    intro z w hzw
    have hsourceValue : sourceVertex z = sourceVertex w := by
      rw [← hdecode z, ← hdecode w, hzw]
    have hsource :
        wholeHierarchyOriginalVertex (leafDeletedCore P)
            (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
            (leafAllocationSpecial P hT) (Sum.inr ⟨z.1.1, z.2⟩) =
          wholeHierarchyOriginalVertex (leafDeletedCore P)
            (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
            (leafAllocationSpecial P hT) (Sum.inr ⟨w.1.1, w.2⟩) := by
      apply Subtype.ext
      exact hsourceValue
    have hver :
        (Sum.inr ⟨z.1.1, z.2⟩ : (leafAllocationHierarchy P hT).Vertex) =
          Sum.inr ⟨w.1.1, w.2⟩ := by
      apply wholeHierarchyOriginalVertex_injective
        (T := leafDeletedCore P) (globalRoot := leafDeletedGlobalRoot P)
        (leafDeletedCore_isTree P hT) (leafAllocationSpecial P hT)
      exact hsource
    have hsigma := Sum.inr.inj hver
    apply Sigma.ext
    · exact Subtype.ext (congrArg Sigma.fst hsigma)
    · exact (Sigma.mk.inj_iff.mp hsigma).2
  have hcard := Fintype.card_le_of_injective f hf
  simpa [LeafSegmentMassCoordinate, BranchMassCoordinate,
    Fintype.card_sigma] using hcard

def leafSegmentDeepWeight
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (i : LeafSegmentIndex P hT) : ℕ :=
  (leafAllocationHierarchy P hT).segments.size i - 1

theorem sum_leafSegmentDeepWeight_add_card
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (I : Finset (LeafSegmentIndex P hT)) :
    (∑ i ∈ I, leafSegmentDeepWeight P hT i) + #I =
      ∑ i ∈ I, (leafAllocationHierarchy P hT).segments.size i := by
  calc
    (∑ i ∈ I, leafSegmentDeepWeight P hT i) + #I =
        (∑ i ∈ I, leafSegmentDeepWeight P hT i) + ∑ _i ∈ I, 1 := by
      simp
    _ = ∑ i ∈ I, (leafSegmentDeepWeight P hT i + 1) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ I,
        (leafAllocationHierarchy P hT).segments.size i := by
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.sub_add_cancel
        (segmented_size_pos
          (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
            (leafDeletedGlobalRoot P)) (leafAllocationSpecial P hT) i)

theorem sum_leafSegmentDeepWeight_le_branchDemand
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (I : Finset (LeafSegmentIndex P hT)) (A : Finset (BranchIndex P))
    (hmass : (∑ i ∈ I,
        (leafAllocationHierarchy P hT).segments.size i) ≤
      ∑ j ∈ A, (branchForest P).branches.size j)
    (hroots : #A ≤ #I) :
    (∑ i ∈ I, leafSegmentDeepWeight P hT i) ≤
      ∑ j ∈ A, ((branchForest P).branches.size j - 1) := by
  have hseg := sum_leafSegmentDeepWeight_add_card P hT I
  have hbranch := sum_branchDeepWeight_add_card P A
  omega

/-- Selected large branches survive the Claim-6.8 leaf deletion. -/
theorem selected_actualBranchRoot_not_mem_originalLeaves
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) (hj : j ∈ S.selected) :
    actualBranchRoot P j ∉ originalLevelOneLeaves P := by
  intro hleaf
  have hsizeOne := (actualBranchRoot_mem_levelOneLeaves_iff P j).mp
    (Finset.mem_inter.mp hleaf).1
  have hjLarge := (mem_largeHalfBranches P j).mp
    (S.selected_available hj)
  omega

/-- Every selected canonical branch contributes its surviving marked root
to a leaf-core hierarchy segment. -/
theorem exists_leafSegmentRoot_of_selectedBranch
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) (hj : j ∈ S.selected) :
    ∃ i : LeafSegmentIndex P hT,
      leafSegmentSourceClass P hT i = Sum.inr j := by
  classical
  let core := leafDeletedCore P
  let coreTree := leafDeletedCore_isTree P hT
  let coreRoot := leafDeletedGlobalRoot P
  let x : LeafDeletedVertex P :=
    ⟨actualBranchRoot P j,
      selected_actualBranchRoot_not_mem_originalLeaves P S j hj⟩
  let F := wholeBranchForest core coreTree coreRoot
  let rawSpecial := (leafCoreMarkedVertices P).image
    (toWholeBranchForestVertex core coreTree coreRoot)
  have hxMarked : x ∈ leafCoreMarkedVertices P := by
    apply (mem_leafCoreMarkedVertices P x).2
    exact actualBranchRoot_mem_allocationMarkedVertices P ∅ j
  have hxImage : toWholeBranchForestVertex core coreTree coreRoot x ∈
      rawSpecial := Finset.mem_image.mpr ⟨x, hxMarked, rfl⟩
  cases hcoord : toWholeBranchForestVertex core coreTree coreRoot x with
  | inl q =>
      have hq : q = 0 := Subsingleton.elim _ _
      have hbad : x = coreRoot := by
        apply toWholeBranchForestVertex_injective core coreTree coreRoot
        rw [hcoord, hq, toWholeBranchForestVertex_root]
      exact False.elim (actualBranchRoot_ne_globalRoot P j
        (congrArg Subtype.val hbad))
  | inr z =>
      have hz : (Sum.inr z : F.Vertex) ∈ rawSpecial := by
        simpa [F, hcoord] using hxImage
      obtain ⟨i, hi⟩ := unflatten_branchSpecial_is_segmentRoot
        F rawSpecial z hz
      have hi' : toWholeHierarchyVertex core coreTree coreRoot
            (leafAllocationSpecial P hT) x =
          (leafAllocationHierarchy P hT).segmentRoot i := by
        change unflatten F (branchSpecial F rawSpecial)
            (toWholeBranchForestVertex core coreTree coreRoot x) = _
        rw [hcoord]
        exact hi
      refine ⟨i, ?_⟩
      have hliteral := congrArg
        (wholeHierarchyOriginalVertex core coreTree coreRoot
          (leafAllocationSpecial P hT)) hi'
      rw [wholeHierarchyOriginal_toWholeHierarchyVertex] at hliteral
      change literalSourceClass P
          (wholeHierarchyOriginalVertex core coreTree coreRoot
            (leafAllocationSpecial P hT)
            ((leafAllocationHierarchy P hT).segmentRoot i)).1 = Sum.inr j
      rw [← hliteral]
      exact literalSourceClass_partitionBranchEquivNonroots P
        (⟨j, (branchForest P).branches.root j⟩ :
          Σ q, Fin ((branchForest P).branches.size q))

theorem card_branch_le_leafSegment_of_rootClasses
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (I : Finset (LeafSegmentIndex P hT)) (A : Finset (BranchIndex P))
    (hroot : ∀ j, j ∈ A → ∃ i ∈ I,
      leafSegmentSourceClass P hT i = Sum.inr j) :
    #A ≤ #I := by
  classical
  let index : (j : {j // j ∈ A}) → LeafSegmentIndex P hT :=
    fun j ↦ Classical.choose (hroot j.1 j.2)
  have index_mem : ∀ j : {j // j ∈ A}, index j ∈ I := fun j ↦
    (Classical.choose_spec (hroot j.1 j.2)).1
  have index_class : ∀ j : {j // j ∈ A},
      leafSegmentSourceClass P hT (index j) = Sum.inr j.1 := fun j ↦
    (Classical.choose_spec (hroot j.1 j.2)).2
  let f : {j // j ∈ A} → {i // i ∈ I} := fun j ↦
    ⟨index j, index_mem j⟩
  have hf : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    apply Sum.inr.inj
    rw [← index_class j, ← index_class k]
    exact congrArg Subtype.val hjk
  simpa using Fintype.card_le_of_injective f hf

end Erdos547b.ZhaoClaim68LeafCoreClassification

#print axioms Erdos547b.ZhaoClaim68LeafCoreClassification.canonicalLeafWholeSourceBoundary
#print axioms Erdos547b.ZhaoClaim68LeafCoreClassification.leafWholeSegment_sourceClass_eq
#print axioms Erdos547b.ZhaoClaim68LeafCoreClassification.leafSegmentClass_cover
#print axioms Erdos547b.ZhaoClaim68LeafCoreClassification.leafSegment_size_le_sourceBranch
