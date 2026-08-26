/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchyAttachments
import ErdosProblems.Erdos547b.Lemma58GroupedSmallForest
import ErdosProblems.Erdos547b.HierarchicalCoordinatePools

/-!
# Endpoint-side accounting for the Claim 6.16 hierarchy

The segmented whole-tree hierarchy and the canonical Zhao branch forest use
different coordinate systems.  This file gives the source-only bridge between
them.  A hierarchy coordinate in a branch-class segment is sent to its literal
canonical branch coordinate.  The map is injective and preserves the rooted
two-colouring, hence the number of hierarchy coordinates assigned to either
oriented matching endpoint is at most the corresponding literal branch-side
load.

This is the direction needed by the coordinate-pool online realization.  It
does not assume an embedding, a host graph, or a continuation certificate.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchyCoordinateSide

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.RegularPair
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim68BranchGraphTransport
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-! ## Literal branch parity -/

/-- A connected graph embedded into a tree has the same distances as the
ambient tree.  The mapped shortest path is the unique ambient path. -/
theorem embedding_dist_eq_of_tree_of_connected
    {A B : Type*} {S : SimpleGraph A} {G : SimpleGraph B}
    (hS : S.Connected) (hG : G.IsTree) (e : S →g G)
    (he : Function.Injective e) (x y : A) :
    S.dist x y = G.dist (e x) (e y) := by
  obtain ⟨p, hpPath, hpLength⟩ := hS.exists_path_of_dist x y
  obtain ⟨q, hqPath, hqLength⟩ :=
    hG.connected.exists_path_of_dist (e x) (e y)
  have hpMapPath : (p.map e).IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective he hpPath
  have hpEq : p.map e = q :=
    (hG.existsUnique_path (e x) (e y)).unique hpMapPath hqPath
  have hlen := congrArg SimpleGraph.Walk.length hpEq
  calc
    S.dist x y = p.length := hpLength.symm
    _ = (p.map e).length := by
      rw [SimpleGraph.Walk.length_map]
    _ = q.length := hlen
    _ = G.dist (e x) (e y) := hqLength

/-- Distances inside one Zhao cut component are literal distances in the
original tree. -/
theorem component_dist_eq_ambient
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (i : Fin P.numParts) (x y : ↑(P.components i)) :
    (P.components i).toSimpleGraph.dist x y = T.dist x.1 y.1 := by
  let e : (P.components i).toSimpleGraph →g T :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        have hcut : P.cutForest.Adj a.1 b.1 :=
          ((P.components i).toSimpleGraph_adj a.2 b.2).mp hab
        exact (T.deleteEdges_le
          (↑(zhaoCutEdges P.roots P.parent) : Set (Sym2 V))) hcut }
  exact embedding_dist_eq_of_tree_of_connected
    (P.components i).connected_toSimpleGraph hT e Subtype.val_injective x y

/-- The distance-parity side used by the strengthened hierarchy is exactly
the canonical rooted two-colouring of the corresponding Zhao branch. -/
theorem canonicalBranchSide_partitionBranchCoordinate
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (j : BranchIndex P)
    (a : Fin ((branchForest P).branches.size j)) :
    canonicalBranchSide P j
        (partitionBranchEquivNonroots P ⟨j, a⟩).1 =
      ((branchForest P).branches.isTree j).coloringTwoOfVert
        ((branchForest P).branches.root j) a := by
  let i : Fin P.numParts := (childKeyEquiv P.orderedForest j).1.1
  let rootLocal : Fin (P.orderedForest.size i) :=
    branchLocalVertex P.orderedForest j ((branchForest P).branches.root j)
  let aLocal : Fin (P.orderedForest.size i) :=
    branchLocalVertex P.orderedForest j a
  let rootC : ↑(P.components i) := P.componentEquiv i rootLocal
  let aC : ↑(P.components i) := P.componentEquiv i aLocal
  have hrootValue : rootC.1 = actualBranchRoot P j := by
    rw [actualBranchRoot_eq_partitionBranchEquiv,
      partitionBranchEquivNonroots_apply_val,
      flattenBranch_branch_eq_local]
    simp only [rootC, rootLocal, i, branchLocalVertex_root]
    rfl
  have haValue : aC.1 = (partitionBranchEquivNonroots P ⟨j, a⟩).1 := by
    rw [partitionBranchEquivNonroots_apply_val,
      flattenBranch_branch_eq_local]
    rfl
  have hdist :
      T.dist (actualBranchRoot P j)
          (partitionBranchEquivNonroots P ⟨j, a⟩).1 =
        ((branchForest P).branches.tree j).dist
          ((branchForest P).branches.root j) a := by
    calc
      T.dist (actualBranchRoot P j)
          (partitionBranchEquivNonroots P ⟨j, a⟩).1 =
          T.dist rootC.1 aC.1 := by rw [hrootValue, haValue]
      _ = (P.components i).toSimpleGraph.dist rootC aC :=
        (component_dist_eq_ambient hT P i rootC aC).symm
      _ = (P.orderedForest.tree i).dist rootLocal aLocal := by
        exact componentEquiv_dist_eq P i rootLocal aLocal
      _ = ((branchForest P).branches.tree j).dist
          ((branchForest P).branches.root j) a := by
        simpa only [i, rootLocal, aLocal, branchLocalVertex_root] using
          (branchTree_dist_eq_component_dist P.orderedForest j a).symm
  apply Fin.ext
  change T.dist (actualBranchRoot P j)
      (partitionBranchEquivNonroots P ⟨j, a⟩).1 % 2 =
    ((branchForest P).branches.tree j).dist
      ((branchForest P).branches.root j) a % 2
  rw [hdist]

/-! ## Side-filtered coordinate sets -/

/-- Hierarchy coordinates belonging to selected segments and sent to one
physical endpoint by the supplied branch orientations. -/
noncomputable def hierarchyCoordinatesAtSide
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (I : Finset (SegmentIndex hT P optional))
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) (c : Fin 2) :
    Finset (Σ i, Fin ((AllocationHierarchy hT P optional).segments.size i)) := by
  classical
  exact Finset.univ.filter fun z ↦
    z.1 ∈ I ∧
      match segmentSourceClass hT P optional z.1 with
      | Sum.inl _ => False
      | Sum.inr j =>
          orient j (segmentEndpointSide hT P optional z.1 j z.2) = c

/-- Literal canonical branch coordinates in a chosen branch family and on
one oriented endpoint. -/
noncomputable def branchCoordinatesAtSide
    (P : ZhaoForestPartition T globalRoot small)
    (A : Finset (BranchIndex P))
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) (c : Fin 2) :
    Finset (Σ j, Fin ((branchForest P).branches.size j)) := by
  classical
  exact Finset.univ.filter fun z ↦
    z.1 ∈ A ∧
      orient z.1 (((branchForest P).branches.isTree z.1).coloringTwoOfVert
        ((branchForest P).branches.root z.1) z.2) = c

/-- Side-filtered hierarchy coordinates inject into the corresponding
literal branch colour classes. -/
theorem card_hierarchyCoordinatesAtSide_le_branchCoordinatesAtSide
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (I : Finset (SegmentIndex hT P optional))
    (A : Finset (BranchIndex P))
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) (c : Fin 2)
    (hbranch : ∀ i ∈ I, ∃ j,
      segmentSourceClass hT P optional i = Sum.inr j)
    (hbranchMem : ∀ i ∈ I, ∀ j,
      segmentSourceClass hT P optional i = Sum.inr j → j ∈ A) :
    #(hierarchyCoordinatesAtSide hT P optional I orient c) ≤
      #(branchCoordinatesAtSide P A orient c) := by
  classical
  let sourceVertex :
      ↑(hierarchyCoordinatesAtSide hT P optional I orient c) → V :=
    fun z ↦ wholeHierarchyOriginalVertex T hT globalRoot
      (AllocationSpecial hT P optional) (Sum.inr z.1)
  have sourceBranch : ∀ z, ∃ j,
      literalSourceClass P (sourceVertex z) = Sum.inr j := by
    intro z
    obtain ⟨j, hj⟩ :=
      hbranch z.1.1 (Finset.mem_filter.mp z.2).2.1
    dsimp only [sourceVertex]
    exact ⟨j, (wholeSegment_sourceClass_eq_of_boundary hT P optional
      (canonicalWholeSourceBoundary hT P optional) z.1.1 z.1.2).trans hj⟩
  have sourceNonroot : ∀ z, sourceVertex z ∉ partitionRoots P := by
    intro z hz
    obtain ⟨j, hzClass⟩ := sourceBranch z
    rw [literalSourceClass_of_root P (sourceVertex z) hz] at hzClass
    cases hzClass
  let sourceCoordinate :
      (z : ↑(hierarchyCoordinatesAtSide hT P optional I orient c)) →
        Σ j, Fin ((branchForest P).branches.size j) :=
    fun z ↦ literalBranchCoordinate P (sourceVertex z) (sourceNonroot z)
  have segmentClass_sourceCoordinate : ∀ z,
      segmentSourceClass hT P optional z.1.1 =
        Sum.inr (sourceCoordinate z).1 := by
    intro z
    have hcoord := literalSourceClass_eq_inr_literalBranchCoordinate P
      (sourceVertex z) (sourceNonroot z)
    exact (wholeSegment_sourceClass_eq_of_boundary hT P optional
      (canonicalWholeSourceBoundary hT P optional) z.1.1 z.1.2).symm.trans
        hcoord
  have sourceCoordinate_mem : ∀ z,
      sourceCoordinate z ∈ branchCoordinatesAtSide P A orient c := by
    intro z
    rw [branchCoordinatesAtSide, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact hbranchMem z.1.1 (Finset.mem_filter.mp z.2).2.1
        (sourceCoordinate z).1 (segmentClass_sourceCoordinate z)
    · have hside := (Finset.mem_filter.mp z.2).2.2
      rw [segmentClass_sourceCoordinate z] at hside
      have hparity := canonicalBranchSide_partitionBranchCoordinate hT P
        (sourceCoordinate z).1 (sourceCoordinate z).2
      have hdecode :
          (partitionBranchEquivNonroots P (sourceCoordinate z)).1 =
            sourceVertex z := by
        exact partitionBranchEquivNonroots_literalBranchCoordinate P
          (sourceVertex z) (sourceNonroot z)
      rw [hdecode] at hparity
      rw [← hparity]
      exact hside
  let f : ↑(hierarchyCoordinatesAtSide hT P optional I orient c) →
      ↑(branchCoordinatesAtSide P A orient c) :=
    fun z ↦ ⟨sourceCoordinate z, sourceCoordinate_mem z⟩
  have hf : Function.Injective f := by
    intro z w hzw
    have hcoord : sourceCoordinate z = sourceCoordinate w :=
      congrArg Subtype.val hzw
    dsimp only [sourceCoordinate] at hcoord
    have hdecoded := congrArg
      (fun q ↦ (partitionBranchEquivNonroots P q).1) hcoord
    have hsource : sourceVertex z = sourceVertex w := by
      simpa only [partitionBranchEquivNonroots_literalBranchCoordinate]
        using hdecoded
    apply Subtype.ext
    apply Sum.inr.inj
    apply wholeHierarchyOriginalVertex_injective hT
      (AllocationSpecial hT P optional)
    exact hsource
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

/-! ## Cardinal form used by Lemma 5.8 -/

private abbrev branchSideFiber
    (P : ZhaoForestPartition T globalRoot small)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) (c : Fin 2)
    (j : BranchIndex P) :=
  ↑(Finset.univ.filter fun a : Fin ((branchForest P).branches.size j) ↦
    orient j (((branchForest P).branches.isTree j).coloringTwoOfVert
      ((branchForest P).branches.root j) a) = c)

noncomputable def branchCoordinatesAtSideEquiv
    (P : ZhaoForestPartition T globalRoot small)
    (A : Finset (BranchIndex P))
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) (c : Fin 2) :
    ↑(branchCoordinatesAtSide P A orient c) ≃
      Σ j : ↑A, branchSideFiber P orient c j.1 where
  toFun z := by
    have hz := (Finset.mem_filter.mp z.2).2
    exact ⟨⟨z.1.1, hz.1⟩,
      ⟨z.1.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.2⟩⟩⟩
  invFun z := by
    exact ⟨⟨z.1.1, z.2.1⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, z.1.2, (Finset.mem_filter.mp z.2.2).2⟩⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Subtype.ext rfl)

theorem card_branchCoordinatesAtSide
    (P : ZhaoForestPartition T globalRoot small)
    (A : Finset (BranchIndex P))
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) (c : Fin 2) :
    #(branchCoordinatesAtSide P A orient c) =
      ∑ j ∈ A, orientedClassSize (branchForest P).branches orient j c := by
  classical
  have hcard := Fintype.card_congr
    (branchCoordinatesAtSideEquiv P A orient c)
  simp only [Fintype.card_coe, Fintype.card_sigma] at hcard
  calc
    #(branchCoordinatesAtSide P A orient c) =
        ∑ j : ↑A, #(Finset.univ.filter fun a :
            Fin ((branchForest P).branches.size j.1) ↦
          orient j.1
            (((branchForest P).branches.isTree j.1).coloringTwoOfVert
              ((branchForest P).branches.root j.1) a) = c) := hcard
    _ = ∑ j ∈ A,
        #(Finset.univ.filter fun a :
            Fin ((branchForest P).branches.size j) ↦
          orient j (((branchForest P).branches.isTree j).coloringTwoOfVert
            ((branchForest P).branches.root j) a) = c) := by
      let f : BranchIndex P → ℕ := fun j ↦
        #(Finset.univ.filter fun a :
            Fin ((branchForest P).branches.size j) ↦
          orient j (((branchForest P).branches.isTree j).coloringTwoOfVert
            ((branchForest P).branches.root j) a) = c)
      change (∑ j : ↑A, f j.1) = ∑ j ∈ A, f j
      exact Finset.sum_attach A f
    _ = ∑ j ∈ A,
        orientedClassSize (branchForest P).branches orient j c := rfl

theorem hierarchy_side_load_le_branch_side_load
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (I : Finset (SegmentIndex hT P optional))
    (A : Finset (BranchIndex P))
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) (c : Fin 2)
    (hbranch : ∀ i ∈ I, ∃ j,
      segmentSourceClass hT P optional i = Sum.inr j)
    (hbranchMem : ∀ i ∈ I, ∀ j,
      segmentSourceClass hT P optional i = Sum.inr j → j ∈ A) :
    #(hierarchyCoordinatesAtSide hT P optional I orient c) ≤
      ∑ j ∈ A, orientedClassSize (branchForest P).branches orient j c := by
  rw [← card_branchCoordinatesAtSide P A orient c]
  exact card_hierarchyCoordinatesAtSide_le_branchCoordinatesAtSide
    hT P optional I A orient c hbranch hbranchMem

/-! ## Direct bridge from coordinate-pool occupancy -/

theorem coordinatePoolLoad_le_hierarchy_side
    {Pool : Type*} [DecidableEq Pool]
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (rootPool : SegmentIndex hT P optional → Pool)
    (interiorPool : (i : SegmentIndex hT P optional) →
      Fin ((AllocationHierarchy hT P optional).segments.size i) → Pool)
    (e : Pool) (I : Finset (SegmentIndex hT P optional))
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) (c : Fin 2)
    (hroot : ∀ i, rootPool i = e →
      (⟨i, (AllocationHierarchy hT P optional).segments.root i⟩ :
        Σ k, Fin ((AllocationHierarchy hT P optional).segments.size k)) ∈
          hierarchyCoordinatesAtSide hT P optional I orient c)
    (hinterior : ∀ i a,
      a ≠ (AllocationHierarchy hT P optional).segments.root i →
      interiorPool i a = e →
      (⟨i, a⟩ :
        Σ k, Fin ((AllocationHierarchy hT P optional).segments.size k)) ∈
          hierarchyCoordinatesAtSide hT P optional I orient c) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        rootPool interiorPool e ≤
      #(hierarchyCoordinatesAtSide hT P optional I orient c) := by
  classical
  rw [coordinatePoolLoad_eq_card_coordinatesAtPool]
  apply Finset.card_le_card
  rintro ⟨i, a⟩ hz
  have hz' := (Finset.mem_filter.mp hz).2
  by_cases hzr : a =
      (AllocationHierarchy hT P optional).segments.root i
  · subst a
    exact hroot i (by simpa using hz')
  · exact hinterior i a hzr
      (by simpa only [if_neg hzr] using hz')

theorem coordinatePoolLoad_le_branch_side_load
    {Pool : Type*} [DecidableEq Pool]
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (rootPool : SegmentIndex hT P optional → Pool)
    (interiorPool : (i : SegmentIndex hT P optional) →
      Fin ((AllocationHierarchy hT P optional).segments.size i) → Pool)
    (e : Pool) (I : Finset (SegmentIndex hT P optional))
    (A : Finset (BranchIndex P))
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) (c : Fin 2)
    (hroot : ∀ i, rootPool i = e →
      (⟨i, (AllocationHierarchy hT P optional).segments.root i⟩ :
        Σ k, Fin ((AllocationHierarchy hT P optional).segments.size k)) ∈
          hierarchyCoordinatesAtSide hT P optional I orient c)
    (hinterior : ∀ i a,
      a ≠ (AllocationHierarchy hT P optional).segments.root i →
      interiorPool i a = e →
      (⟨i, a⟩ :
        Σ k, Fin ((AllocationHierarchy hT P optional).segments.size k)) ∈
          hierarchyCoordinatesAtSide hT P optional I orient c)
    (hbranch : ∀ i ∈ I, ∃ j,
      segmentSourceClass hT P optional i = Sum.inr j)
    (hbranchMem : ∀ i ∈ I, ∀ j,
      segmentSourceClass hT P optional i = Sum.inr j → j ∈ A) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        rootPool interiorPool e ≤
      ∑ j ∈ A,
        orientedClassSize (branchForest P).branches orient j c := by
  exact (coordinatePoolLoad_le_hierarchy_side hT P optional rootPool
    interiorPool e I orient c hroot hinterior).trans
      (hierarchy_side_load_le_branch_side_load hT P optional I A orient c
        hbranch hbranchMem)

end Erdos547b.ZhaoClaim616HierarchyCoordinateSide

#print axioms Erdos547b.ZhaoClaim616HierarchyCoordinateSide.canonicalBranchSide_partitionBranchCoordinate
#print axioms Erdos547b.ZhaoClaim616HierarchyCoordinateSide.hierarchy_side_load_le_branch_side_load
#print axioms Erdos547b.ZhaoClaim616HierarchyCoordinateSide.coordinatePoolLoad_le_branch_side_load
