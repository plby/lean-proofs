/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichCoordinatePairFacts

/-!
# Branchwise-oriented pair facts for coordinate Claim 6.15

This is the source-faithful pair layer used by Zhao Lemma 5.8.  Unlike the
canonical fixed-side wrapper, roots assigned to the same matching edge may
choose different endpoints.  The three source-facing hypotheses are therefore
stated for the actual branch root side `orient j 0`.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichCoordinateOrientedPairFacts

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616CoordinateCutParents
open Erdos547b.ZhaoClaim616CoordinateCutAttachmentParity
open Erdos547b.ZhaoClaim616CoordinateCanonicalOptional
open Erdos547b.ZhaoClaim616CoordinateSourceParity
open Erdos547b.ZhaoClaim616RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615CoordinateOrientation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools
open Erdos547b.ZhaoClaim615RichCoordinateApplication
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoHierarchicalCoordinateContainment
open Erdos547b.ZhaoLemma614HierarchicalFullTree
open Erdos547b.ZhaoLemma59HierarchicalRegular

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)

section Source

variable
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {K0 K1 Kb : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → MatchingEdge Q.claim67.M)
    (edge1 : K1 → MatchingEdge Q.claim67.M)
    (edgeb : Kb → MatchingEdge Q.claim67.M)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)

private abbrev pairRootSlot :=
  coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
    (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A edge0 edge1
    edgeb (orient)

private abbrev pairInteriorSlot :=
  coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S capacity0
    capacity1 capacityb A edge0 edge1 edgeb
      (orient)

private abbrev sourceSlot : RichSlot Pcluster Gdegree threshold quota R miss Q :=
  Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)

private theorem branchClass_mem_selected_or_residual_or_minor'
    (havailable : available ⊆ halfBranches P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) :
    j ∈ S.selected ∨ j ∈ majorResidualBranches P S ∨ j ∈ minorBranches P := by
  by_cases hjHalf : j ∈ halfBranches P
  · by_cases hj : j ∈ S.selected
    · exact Or.inl hj
    · exact Or.inr (Or.inl ((mem_majorResidualBranches P S j).2 ⟨hjHalf, hj⟩))
  · right; right
    have hj : j ∈ halfBranches P ∪ minorBranches P := by
      rw [halfBranches_union_minorBranches]
      exact Finset.mem_univ _
    exact (Finset.mem_union.mp hj).resolve_left hjHalf

/-- Direct hierarchy children use either the opposite distinguished reserve
or the source-facing endpoint chosen for their branch family. -/
theorem orientedDirectPair
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ j, j ∈ S.selected → (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 (A.F0edge j)).1 (orient j 0)))
    (hroot1 : ∀ j, j ∈ majorResidualBranches P S →
      (padGraph R).Adj (Sum.inl Q.A)
        (matchingEdgeEndpoint (edge1 (A.F1edge j)).1 (orient j 0)))
    (hrootb : ∀ j, j ∈ minorBranches P → (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb (A.Fbedge j)).1 (orient j 0)))
    (i : SegmentIndex hT P (canonicalOptional P))
    (hparent : (AllocationHierarchy hT P (canonicalOptional P)).parent i =
      Sum.inl 0) :
    G.IsUniform rho
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (sourceSlot Pcluster Gdegree threshold quota R miss Q P))
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i)) ∧
      density ≤ G.edgeDensity
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (sourceSlot Pcluster Gdegree threshold quota R miss Q P))
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i)) := by
  apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho density H
  have hi : SegmentRootOriginal hT P (canonicalOptional P) i ∉ (∅ : Finset V) :=
    by simp
  rcases directSegment_sourceClass hT P (canonicalOptional P) i hparent with
        hcomponent | hbranch
  · obtain ⟨q, hclass, -⟩ := hcomponent
    rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i = Sum.inl (componentReservoirSide P q) by
        exact coordinateHierarchyRootSlot_component hT P (canonicalOptional P)
          ∅ (sourceVertexReservoirSide P) S capacity0
          capacity1 capacityb A edge0 edge1 edgeb
          (orient) i q hi hclass]
    apply reserveVertices_adj_of_ne Pcluster Gdegree threshold quota R miss Q
    exact (directComponentReservoirSide_ne hT P (canonicalOptional P) i q
      hparent hclass).symm
  · obtain ⟨j, hclass, howner, _hroot⟩ := hbranch
    rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i = coordinateBranchSlot P S capacity0 capacity1 capacityb A
            edge0 edge1 edgeb
              (orient) j 0 by
        change coordinateHierarchyRootSlot hT P (canonicalOptional P)
          ∅ (sourceVertexReservoirSide P) S capacity0
          capacity1 capacityb A edge0 edge1 edgeb
            (orient) i = _
        rw [coordinateHierarchyRootSlot_branch hT P (canonicalOptional P)
          ∅ (sourceVertexReservoirSide P) S capacity0
          capacity1 capacityb A edge0 edge1 edgeb
            (orient) i j hi hclass]
        congr 1
        exact segmentEndpointSide_root_zero_of_optionalParity hT P
          (canonicalOptional P) (canonicalOptional_parity hT P) i j hclass]
    rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j with
          hj | hj | hj
    · have hside := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
        P j (havailable (S.selected_available hj))
      rw [howner] at hside
      simp [sourceSlot, richSlotVertex, coordinateBranchSlot,
        coordinateBranchEdge, hj, hside]
      exact hroot0 j hj
    · have hside := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
        P j ((mem_majorResidualBranches P S j).mp hj).1
      rw [howner] at hside
      have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
      simp [sourceSlot, richSlotVertex, coordinateBranchSlot,
        coordinateBranchEdge, hj0, hj, hside]
      exact hroot1 j hj
    · have hside :=
        componentReservoirSide_owner_eq_one_of_mem_minorBranches P j hj
      rw [howner] at hside
      have hjHalf : j ∉ halfBranches P := by
        intro h
        exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
          h hj
      have hj0 : j ∉ S.selected := fun h ↦
        hjHalf (havailable (S.selected_available h))
      have hj1 : j ∉ majorResidualBranches P S := by
        intro h
        exact hjHalf ((mem_majorResidualBranches P S j).mp h).1
      simp [sourceSlot, richSlotVertex, coordinateBranchSlot,
        coordinateBranchEdge, hj0, hj1, hside]
      exact hrootb j hj

/-- A component-root attachment is either an edge between the two root
reservoirs or the reverse of the source-facing root pair of its parent
branch. -/
theorem orientedComponentAttachmentPair
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ j, j ∈ S.selected → (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 (A.F0edge j)).1 (orient j 0)))
    (hroot1 : ∀ j, j ∈ majorResidualBranches P S →
      (padGraph R).Adj (Sum.inl Q.A)
        (matchingEdgeEndpoint (edge1 (A.F1edge j)).1 (orient j 0)))
    (hrootb : ∀ j, j ∈ minorBranches P → (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb (A.Fbedge j)).1 (orient j 0)))
    (i k : SegmentIndex hT P (canonicalOptional P))
    (a : Fin ((AllocationHierarchy hT P (canonicalOptional P)).segments.size k))
    (q : Fin P.numParts)
    (hi : segmentSourceClass hT P (canonicalOptional P) i = Sum.inl q)
    (hparent : (AllocationHierarchy hT P (canonicalOptional P)).parent i =
      Sum.inr ⟨k, a⟩) :
    G.IsUniform rho
        (HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P (canonicalOptional P))
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l b ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb orient l b)) k a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i)) ∧
      density ≤ G.edgeDensity
        (HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P (canonicalOptional P))
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l b ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb orient l b)) k a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i)) := by
  have haRoot := componentRoot_attachment_coordinate_eq_segmentRoot hT P
    (canonicalOptional P) (canonicalOptional_covers_cutParents P) i k a q hi
    hparent
  rw [HierarchicalSegmentForest.rawCandidate, if_pos haRoot]
  apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho density H
  have hiEmpty : SegmentRootOriginal hT P (canonicalOptional P) i ∉
      (∅ : Finset V) := by simp
  rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
        capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i = Sum.inl (componentReservoirSide P q) by
      exact coordinateHierarchyRootSlot_component hT P (canonicalOptional P) ∅
        (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A edge0
        edge1 edgeb _ i q hiEmpty hi]
  cases hk : segmentSourceClass hT P (canonicalOptional P) k with
  | inl r =>
      have hkEmpty : SegmentRootOriginal hT P (canonicalOptional P) k ∉
          (∅ : Finset V) := by simp
      rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient k = Sum.inl (componentReservoirSide P r) by
          exact coordinateHierarchyRootSlot_component hT P (canonicalOptional P)
            ∅ (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
            edge0 edge1 edgeb _ k r hkEmpty hk]
      apply reserveVertices_adj_of_ne Pcluster Gdegree threshold quota R miss Q
      have hrootI : SegmentRootOriginal hT P (canonicalOptional P) i =
          P.roots q := (literalSourceClass_eq_inl_iff P _ q).mp hi
      have hrootK : SegmentRootOriginal hT P (canonicalOptional P) k =
          P.roots r := (literalSourceClass_eq_inl_iff P _ r).mp hk
      have hparentOriginal : SegmentParentOriginal hT P (canonicalOptional P) i =
          SegmentRootOriginal hT P (canonicalOptional P) k := by
        unfold SegmentParentOriginal SegmentRootOriginal
        rw [hparent, haRoot]
        rfl
      have hadj : T.Adj (P.roots r) (P.roots q) := by
        rw [← hrootK, ← hrootI, ← hparentOriginal,
          segmentParentOriginal_eq_treeParent]
        exact TreePartition.parent_adj hT globalRoot
          (segmentRootOriginal_ne_globalRoot hT P (canonicalOptional P) i)
      have hne := sourceVertexReservoirSide_ne_of_adj hT P hadj
      simpa only [sourceVertexReservoirSide_root] using hne
  | inr j =>
      have hkEmpty : SegmentRootOriginal hT P (canonicalOptional P) k ∉
          (∅ : Finset V) := by simp
      have hrootSide := segmentEndpointSide_root_zero_of_optionalParity hT P
        (canonicalOptional P) (canonicalOptional_parity hT P) k j hk
      rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient k = coordinateBranchSlot P S capacity0 capacity1 capacityb
              A edge0 edge1 edgeb
                (orient) j 0 by
          change coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
            (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
            edge0 edge1 edgeb _ k = _
          rw [coordinateHierarchyRootSlot_branch hT P (canonicalOptional P) ∅
            (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
            edge0 edge1 edgeb _ k j hkEmpty hk]
          congr 1]
      have hside := componentRoot_cutAttachment_parity hT P
        (canonicalOptional P) i k a q j hi hparent hk
      rw [haRoot, hrootSide] at hside
      rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j with
          hj | hj | hj
      · have howner := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
          P j (havailable (S.selected_available hj))
        rw [howner] at hside
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          hj, hside] using (hroot0 j hj).symm
      · have howner := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
          P j ((mem_majorResidualBranches P S j).mp hj).1
        rw [howner] at hside
        have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          hj0, hj, hside] using (hroot1 j hj).symm
      · have howner := componentReservoirSide_owner_eq_one_of_mem_minorBranches
          P j hj
        rw [howner] at hside
        have hjHalf : j ∉ halfBranches P := by
          intro h
          exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
            h hj
        have hj0 : j ∉ S.selected := fun h ↦
          hjHalf (havailable (S.selected_available h))
        have hj1 : j ∉ majorResidualBranches P S := by
          intro h
          exact hjHalf ((mem_majorResidualBranches P S j).mp h).1
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          hj0, hj1, hside] using (hrootb j hj).symm

/-- A branch segment is attached either to its owner component reservoir or
to the opposite endpoint of the same assigned matching edge. -/
theorem orientedBranchAttachmentPair
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ j, j ∈ S.selected → (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 (A.F0edge j)).1 (orient j 0)))
    (hroot1 : ∀ j, j ∈ majorResidualBranches P S →
      (padGraph R).Adj (Sum.inl Q.A)
        (matchingEdgeEndpoint (edge1 (A.F1edge j)).1 (orient j 0)))
    (hrootb : ∀ j, j ∈ minorBranches P → (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb (A.Fbedge j)).1 (orient j 0)))
    (i k : SegmentIndex hT P (canonicalOptional P))
    (a : Fin ((AllocationHierarchy hT P (canonicalOptional P)).segments.size k))
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hi : segmentSourceClass hT P (canonicalOptional P) i = Sum.inr j)
    (hparent : (AllocationHierarchy hT P (canonicalOptional P)).parent i =
      Sum.inr ⟨k, a⟩) :
    G.IsUniform rho
        (HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P (canonicalOptional P))
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l b ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb orient l b)) k a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i)) ∧
      density ≤ G.edgeDensity
        (HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P (canonicalOptional P))
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l b ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb orient l b)) k a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i)) := by
  have hiEmpty : SegmentRootOriginal hT P (canonicalOptional P) i ∉
      (∅ : Finset V) := by simp
  have hrootSide := segmentEndpointSide_root_zero_of_optionalParity hT P
    (canonicalOptional P) (canonicalOptional_parity hT P) i j hi
  rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
        capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i = coordinateBranchSlot P S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb
            (orient) j 0 by
      change coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
        (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A edge0
        edge1 edgeb _ i = _
      rw [coordinateHierarchyRootSlot_branch hT P (canonicalOptional P) ∅
        (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A edge0
        edge1 edgeb _ i j hiEmpty hi]
      congr 1]
  rcases segment_attachment_of_branch_class hT P (canonicalOptional P) i j hi
      with hcanonical | hlater
  · have hparentValue :
        wholeHierarchyOriginalVertex T hT globalRoot
            (AllocationSpecial hT P (canonicalOptional P)) (Sum.inr ⟨k, a⟩) =
          P.roots ((branchForest P).owner j) := by
      calc
        _ = SegmentParentOriginal hT P (canonicalOptional P) i := congrArg
          (wholeHierarchyOriginalVertex T hT globalRoot
            (AllocationSpecial hT P (canonicalOptional P))) hparent.symm
        _ = _ := hcanonical.2
    have hkclass : segmentSourceClass hT P (canonicalOptional P) k =
        Sum.inl ((branchForest P).owner j) := by
      have hc := wholeSegment_sourceClass_eq_of_boundary hT P
        (canonicalOptional P) (canonicalWholeSourceBoundary hT P
          (canonicalOptional P)) k a
      have hrootClass : literalSourceClass P
          (P.roots ((branchForest P).owner j)) =
            Sum.inl ((branchForest P).owner j) :=
        (literalSourceClass_eq_inl_iff P _ _).mpr rfl
      rw [hparentValue, hrootClass] at hc
      exact hc.symm
    have hkRoot : k ∈ rootSegments hT P (canonicalOptional P) :=
      (mem_rootSegments_iff hT P (canonicalOptional P) k).2
        ⟨(branchForest P).owner j, hkclass⟩
    have hkSize := rootSegment_size_eq_one hT P (canonicalOptional P) k hkRoot
    have haRoot : a =
        (AllocationHierarchy hT P (canonicalOptional P)).segments.root k := by
      apply Fin.ext
      have haLt := a.isLt
      have hrLt :=
        ((AllocationHierarchy hT P (canonicalOptional P)).segments.root k).isLt
      omega
    rw [HierarchicalSegmentForest.rawCandidate, if_pos haRoot]
    have hkEmpty : SegmentRootOriginal hT P (canonicalOptional P) k ∉
        (∅ : Finset V) := by simp
    rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient k = Sum.inl
            (componentReservoirSide P ((branchForest P).owner j)) by
        exact coordinateHierarchyRootSlot_component hT P (canonicalOptional P)
          ∅ (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb _ k ((branchForest P).owner j) hkEmpty hkclass]
    apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho density H
    rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j with
        hj | hj | hj
    · have howner := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
        P j (havailable (S.selected_available hj))
      simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        hj, howner] using hroot0 j hj
    · have howner := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
        P j ((mem_majorResidualBranches P S j).mp hj).1
      have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
      simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        hj0, hj, howner] using hroot1 j hj
    · have howner := componentReservoirSide_owner_eq_one_of_mem_minorBranches
        P j hj
      have hjHalf : j ∉ halfBranches P := by
        intro h
        exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
          h hj
      have hj0 : j ∉ S.selected := fun h ↦
        hjHalf (havailable (S.selected_available h))
      have hj1 : j ∉ majorResidualBranches P S := by
        intro h
        exact hjHalf ((mem_majorResidualBranches P S j).mp h).1
      simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        hj0, hj1, howner] using hrootb j hj
  · obtain ⟨l, b, hlparent, -, hlclass⟩ := hlater
    have hsigma : (⟨l, b⟩ : Σ m,
        Fin ((AllocationHierarchy hT P (canonicalOptional P)).segments.size m)) =
        ⟨k, a⟩ := Sum.inr.inj (hlparent.symm.trans hparent)
    cases hsigma
    have haNe := sameBranchAttachment_parent_ne_segmentRoot hT P
      (canonicalOptional P) (canonicalOptional_parity hT P) i k j a hi hlclass
      hparent
    rw [HierarchicalSegmentForest.rawCandidate, if_neg haNe]
    have hside : segmentEndpointSide hT P (canonicalOptional P) k j a = 1 := by
      change canonicalBranchSide P j
        (wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P (canonicalOptional P)) (Sum.inr ⟨k, a⟩)) = 1
      rw [← hparent]
      exact segmentParent_side_one_of_optionalParity hT P (canonicalOptional P)
        (canonicalOptional_parity hT P) i j hi
    rw [show pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient k a = coordinateBranchSlot P S capacity0 capacity1 capacityb
            A edge0 edge1 edgeb
              (orient) j 1 by
        change coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb _ k a = _
        rw [coordinateHierarchyInteriorSlot_branch hT P (canonicalOptional P) S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb _ k j hlclass a,
          hside]]
    apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho density H
    have hne :
        (orient j) 1 ≠
        (orient j) 0 := by
      intro h
      exact one_ne_zero
        ((orient j).injective h)
    rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j with
        hj | hj | hj
    · simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        hj] using matchingVertices_adj_of_ne Pcluster Gdegree
          threshold quota R miss Q (edge0 (A.F0edge j)) _ _ hne
    · have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
      simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        hj0, hj] using matchingVertices_adj_of_ne Pcluster Gdegree
          threshold quota R miss Q (edge1 (A.F1edge j)) _ _ hne
    · have hjHalf : j ∉ halfBranches P := by
        intro h
        exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
          h hj
      have hj0 : j ∉ S.selected := fun h ↦
        hjHalf (havailable (S.selected_available h))
      have hj1 : j ∉ majorResidualBranches P S := by
        intro h
        exact hjHalf ((mem_majorResidualBranches P S j).mp h).1
      simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        hj0, hj1] using matchingVertices_adj_of_ne Pcluster Gdegree
          threshold quota R miss Q (edgeb (A.Fbedge j)) _ _ hne

/-- Every internal edge of a branch segment uses the two opposite endpoints
of that branch's assigned matching edge.  Component-root segments are
singletons, so they have no internal edge. -/
theorem orientedInternalPair
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (i : SegmentIndex hT P (canonicalOptional P))
    (a b : Fin
      ((AllocationHierarchy hT P (canonicalOptional P)).segments.size i))
    (hab : ((AllocationHierarchy hT P
      (canonicalOptional P)).segments.tree i).Adj a b)
    (hb : b ≠
      (AllocationHierarchy hT P (canonicalOptional P)).segments.root i) :
    G.IsUniform rho
        (HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P (canonicalOptional P))
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l c ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb orient l c)) i a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i b)) ∧
      density ≤ G.edgeDensity
        (HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P (canonicalOptional P))
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l c ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb orient l c)) i a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i b)) := by
  generalize hiclass :
      segmentSourceClass hT P (canonicalOptional P) i = sourceClass
  rcases sourceClass with q | j
  · have hiRoot : i ∈ rootSegments hT P (canonicalOptional P) :=
      (mem_rootSegments_iff hT P (canonicalOptional P) i).2 ⟨q, hiclass⟩
    have hiSize := rootSegment_size_eq_one hT P (canonicalOptional P) i hiRoot
    exfalso
    apply hb
    apply Fin.ext
    have hbLt := b.isLt
    have hrLt :=
      ((AllocationHierarchy hT P (canonicalOptional P)).segments.root i).isLt
    omega
  · have horiginal :=
      Erdos547b.ZhaoClaim616RichCoordinatePairFacts.segmentInternal_original_adj
        hT P (canonicalOptional P) i a b hab
    have hsideNe :
        segmentEndpointSide hT P (canonicalOptional P) i j a ≠
          segmentEndpointSide hT P (canonicalOptional P) i j b :=
      canonicalBranchSide_ne_of_adj hT P j horiginal
    have hphysicalNe :
        (orient j)
            (segmentEndpointSide hT P (canonicalOptional P) i j a) ≠
        (orient j)
            (segmentEndpointSide hT P (canonicalOptional P) i j b) := by
      intro heq
      exact hsideNe
        ((orient j).injective heq)
    have hslotA := coordinateHierarchyInteriorSlot_branch hT P
      (canonicalOptional P) S capacity0 capacity1 capacityb A edge0 edge1 edgeb
      (orient) i j hiclass a
    have hslotB := coordinateHierarchyInteriorSlot_branch hT P
      (canonicalOptional P) S capacity0 capacity1 capacityb A edge0 edge1 edgeb
      (orient) i j hiclass b
    by_cases ha :
        a = (AllocationHierarchy hT P (canonicalOptional P)).segments.root i
    · have hrootSide := segmentEndpointSide_root_zero_of_optionalParity hT P
        (canonicalOptional P) (canonicalOptional_parity hT P) i j hiclass
      rw [HierarchicalSegmentForest.rawCandidate, if_pos ha]
      have hiEmpty : SegmentRootOriginal hT P (canonicalOptional P) i ∉
          (∅ : Finset V) := by simp
      rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i = coordinateBranchSlot P S capacity0
              capacity1 capacityb A edge0 edge1 edgeb
                (orient) j 0 by
          change coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
            (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
            edge0 edge1 edgeb _ i = _
          rw [coordinateHierarchyRootSlot_branch hT P (canonicalOptional P) ∅
            (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
            edge0 edge1 edgeb _ i j hiEmpty hiclass]
          congr 1,
        show pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i b = coordinateBranchSlot P S capacity0
              capacity1 capacityb A edge0 edge1 edgeb
                (orient) j
                    (segmentEndpointSide hT P (canonicalOptional P) i j b) by
          exact hslotB]
      apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho
        density H
      rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j
          with hj | hj | hj
      · simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          hj, ha, hrootSide] using
            matchingVertices_adj_of_ne Pcluster Gdegree threshold quota R miss Q
              (edge0 (A.F0edge j)) _ _ hphysicalNe
      · have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          hj0, hj, ha, hrootSide] using
            matchingVertices_adj_of_ne Pcluster Gdegree threshold quota R miss Q
              (edge1 (A.F1edge j)) _ _ hphysicalNe
      · have hjHalf : j ∉ halfBranches P := by
          intro h
          exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
            h hj
        have hj0 : j ∉ S.selected := fun h ↦
          hjHalf (havailable (S.selected_available h))
        have hj1 : j ∉ majorResidualBranches P S := by
          intro h
          exact hjHalf ((mem_majorResidualBranches P S j).mp h).1
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          hj0, hj1, ha, hrootSide] using
            matchingVertices_adj_of_ne Pcluster Gdegree threshold quota R miss Q
              (edgeb (A.Fbedge j)) _ _ hphysicalNe
    · rw [HierarchicalSegmentForest.rawCandidate, if_neg ha,
        show pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i a = coordinateBranchSlot P S capacity0
              capacity1 capacityb A edge0 edge1 edgeb
                (orient) j
                    (segmentEndpointSide hT P (canonicalOptional P) i j a) by
          exact hslotA,
        show pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i b = coordinateBranchSlot P S capacity0
              capacity1 capacityb A edge0 edge1 edgeb
                (orient) j
                    (segmentEndpointSide hT P (canonicalOptional P) i j b) by
          exact hslotB]
      apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho
        density H
      rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j
          with hj | hj | hj
      · simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          hj] using matchingVertices_adj_of_ne Pcluster Gdegree
            threshold quota R miss Q (edge0 (A.F0edge j)) _ _ hphysicalNe
      · have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          hj0, hj] using matchingVertices_adj_of_ne Pcluster Gdegree
            threshold quota R miss Q (edge1 (A.F1edge j)) _ _ hphysicalNe
      · have hjHalf : j ∉ halfBranches P := by
          intro h
          exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
            h hj
        have hj0 : j ∉ S.selected := fun h ↦
          hjHalf (havailable (S.selected_available h))
        have hj1 : j ∉ majorResidualBranches P S := by
          intro h
          exact hjHalf ((mem_majorResidualBranches P S j).mp h).1
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          hj0, hj1] using matchingVertices_adj_of_ne Pcluster
            Gdegree threshold quota R miss Q (edgeb (A.Fbedge j)) _ _
              hphysicalNe

/-- The literal rich host supplies all six regular-pair obligations for the
canonical cut-parent segmentation with no distinguished branch vertices.
The only inputs are padded reduced-graph realization and the three genuine
source-facing adjacency rows. -/
theorem orientedCoordinatePairFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ j, j ∈ S.selected → (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 (A.F0edge j)).1 (orient j 0)))
    (hroot1 : ∀ j, j ∈ majorResidualBranches P S →
      (padGraph R).Adj (Sum.inl Q.A)
        (matchingEdgeEndpoint (edge1 (A.F1edge j)).1 (orient j 0)))
    (hrootb : ∀ j, j ∈ minorBranches P → (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb (A.Fbedge j)).1 (orient j 0))) :
    CoordinateHierarchyPairFacts
      (AllocationHierarchy hT P (canonicalOptional P)) G rho density
      (slotWhole Pcluster Gdegree threshold quota R miss Q
        (sourceSlot Pcluster Gdegree threshold quota R miss Q P))
      (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
        capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
      (slotWhole Pcluster Gdegree threshold quota R miss Q)
      (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
        capacity0 capacity1 capacityb A edge0 edge1 edgeb orient) := by
  refine
    { direct_uniform := fun i hp ↦ ?_
      direct_density := fun i hp ↦ ?_
      attach_uniform := fun i k a hp ↦ ?_
      attach_density := fun i k a hp ↦ ?_
      internal_uniform := fun i a b hab hb ↦ ?_
      internal_density := fun i a b hab hb ↦ ?_ }
  · exact (orientedDirectPair Pcluster Gdegree threshold quota R miss Q hT P S
      capacity0 capacity1 capacityb A edge0 edge1 edgeb orient G rho density H havailable hroot0 hroot1 hrootb i hp).1
  · exact (orientedDirectPair Pcluster Gdegree threshold quota R miss Q hT P S
      capacity0 capacity1 capacityb A edge0 edge1 edgeb orient G rho density H havailable hroot0 hroot1 hrootb i hp).2
  · cases hi : segmentSourceClass hT P (canonicalOptional P) i with
    | inl q =>
        exact (orientedComponentAttachmentPair Pcluster Gdegree threshold quota
          R miss Q hT P S capacity0 capacity1 capacityb A edge0 edge1 edgeb
          orient G rho density H havailable hroot0
          hroot1 hrootb i k a q hi hp).1
    | inr j =>
        exact (orientedBranchAttachmentPair Pcluster Gdegree threshold quota R
          miss Q hT P S capacity0 capacity1 capacityb A edge0 edge1 edgeb
          orient G rho density H havailable hroot0
          hroot1 hrootb i k a j hi hp).1
  · cases hi : segmentSourceClass hT P (canonicalOptional P) i with
    | inl q =>
        exact (orientedComponentAttachmentPair Pcluster Gdegree threshold quota
          R miss Q hT P S capacity0 capacity1 capacityb A edge0 edge1 edgeb
          orient G rho density H havailable hroot0
          hroot1 hrootb i k a q hi hp).2
    | inr j =>
        exact (orientedBranchAttachmentPair Pcluster Gdegree threshold quota R
          miss Q hT P S capacity0 capacity1 capacityb A edge0 edge1 edgeb
          orient G rho density H havailable hroot0
          hroot1 hrootb i k a j hi hp).2
  · exact (orientedInternalPair Pcluster Gdegree threshold quota R miss Q hT P
      S capacity0 capacity1 capacityb A edge0 edge1 edgeb orient G rho density H havailable i a b hab hb).1
  · exact (orientedInternalPair Pcluster Gdegree threshold quota R miss Q hT P
      S capacity0 capacity1 capacityb A edge0 edge1 edgeb orient G rho density H havailable i a b hab hb).2

end Source


end Erdos547b.ZhaoClaim615RichCoordinateOrientedPairFacts

#print axioms Erdos547b.ZhaoClaim615RichCoordinateOrientedPairFacts.orientedDirectPair
#print axioms Erdos547b.ZhaoClaim615RichCoordinateOrientedPairFacts.orientedCoordinatePairFacts
