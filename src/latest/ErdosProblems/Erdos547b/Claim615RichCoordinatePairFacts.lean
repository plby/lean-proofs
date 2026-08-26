/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615CoordinateOrientation
import ErdosProblems.Erdos547b.Claim615RichCoordinateApplication
import ErdosProblems.Erdos547b.Claim616CoordinateCanonicalOptional
import ErdosProblems.Erdos547b.Claim616CoordinateSourceParity
import ErdosProblems.Erdos547b.Claim616RichCoordinatePairFacts

/-!
# Concrete pair facts for coordinate Claim 6.15

The only host input in this module is reduced-graph adjacency.  It classifies
the source edge represented by each hierarchy attachment and converts that
adjacency into the six regular-pair obligations of the coordinate backend.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichCoordinatePairFacts

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

abbrev RichSlot :=
  ZhaoClaim615CoordinateSourceAllocation.RootSlot (MatchingEdge Q.claim67.M)

/-- The padded reduced-graph vertex represented by one literal host slot. -/
def richSlotVertex : RichSlot Pcluster Gdegree threshold quota R miss Q →
    EvenPadding I
  | Sum.inl side => if side = 0 then Sum.inl Q.A else Sum.inl Q.B
  | Sum.inr ⟨e, side⟩ => matchingEdgeEndpoint e.1 side

@[simp] theorem slotWhole_eq_padCluster (slot : RichSlot Pcluster Gdegree
    threshold quota R miss Q) :
    slotWhole Pcluster Gdegree threshold quota R miss Q slot =
      padCluster (clusterVertices Pcluster)
        (richSlotVertex Pcluster Gdegree threshold quota R miss Q slot) := by
  rcases slot with side | edgeSide
  · fin_cases side <;> simp [slotWhole, richSlotVertex, padCluster]
  · rcases edgeSide with ⟨e, side⟩
    rfl

/-- Host regular pairs are obtained uniformly from padded reduced adjacency. -/
structure ReducedPairRealization
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ) : Prop where
  pair_of_adj : ∀ x y, (padGraph R).Adj x y →
    G.IsUniform rho
        (padCluster (clusterVertices Pcluster) x)
        (padCluster (clusterVertices Pcluster) y) ∧
      density ≤ G.edgeDensity
        (padCluster (clusterVertices Pcluster) x)
        (padCluster (clusterVertices Pcluster) y)

private theorem isUniform_real_of_rat
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    {epsilon : ℚ} {X Y : Finset Bv}
    (h : G.IsUniform epsilon X Y) :
    G.IsUniform (epsilon : ℝ) X Y := by
  intro X' hX' Y' hY' hXlarge hYlarge
  have hXlargeQ : (#X : ℚ) * epsilon ≤ (#X' : ℚ) := by
    exact_mod_cast hXlarge
  have hYlargeQ : (#Y : ℚ) * epsilon ≤ (#Y' : ℚ) := by
    exact_mod_cast hYlarge
  exact_mod_cast h hX' hY' hXlargeQ hYlargeQ

/-- The regularity reduced graph itself supplies the realization record;
no per-pair premise remains at applications. -/
theorem reducedPairRealization_of_graph_eq
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (epsilon density : ℚ)
    (hgraph : padGraph R = regularityReducedGraph G
      (padCluster (clusterVertices Pcluster)) epsilon density) :
    ReducedPairRealization Pcluster R G (epsilon : ℝ) (density : ℝ) := by
  refine ⟨?_⟩
  intro x y hxy
  have hred : (regularityReducedGraph G
      (padCluster (clusterVertices Pcluster)) epsilon density).Adj x y := by
    rw [← hgraph]
    exact hxy
  exact ⟨isUniform_real_of_rat G hred.2.1, by exact_mod_cast hred.2.2⟩

theorem wholePair_of_adj
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (x y : RichSlot Pcluster Gdegree threshold quota R miss Q)
    (hxy : (padGraph R).Adj
      (richSlotVertex Pcluster Gdegree threshold quota R miss Q x)
      (richSlotVertex Pcluster Gdegree threshold quota R miss Q y)) :
    G.IsUniform rho
        (slotWhole Pcluster Gdegree threshold quota R miss Q x)
        (slotWhole Pcluster Gdegree threshold quota R miss Q y) ∧
      density ≤ G.edgeDensity
        (slotWhole Pcluster Gdegree threshold quota R miss Q x)
        (slotWhole Pcluster Gdegree threshold quota R miss Q y) := by
  simpa only [slotWhole_eq_padCluster] using H.pair_of_adj _ _ hxy

theorem reserveVertices_adj_of_ne (s t : Fin 2) (hst : s ≠ t) :
    (padGraph R).Adj
      (richSlotVertex Pcluster Gdegree threshold quota R miss Q (Sum.inl s))
      (richSlotVertex Pcluster Gdegree threshold quota R miss Q
        (Sum.inl t)) := by
  fin_cases s <;> fin_cases t
  · exact False.elim (hst rfl)
  · simpa [richSlotVertex] using Q.adj
  · simpa [richSlotVertex] using Q.adj.symm
  · exact False.elim (hst rfl)

theorem matchingVertices_adj_of_ne
    (e : MatchingEdge Q.claim67.M) (s t : Fin 2) (hst : s ≠ t) :
    (padGraph R).Adj
      (richSlotVertex Pcluster Gdegree threshold quota R miss Q
        (Sum.inr ⟨e, s⟩))
      (richSlotVertex Pcluster Gdegree threshold quota R miss Q
        (Sum.inr ⟨e, t⟩)) := by
  have h01 := matchingEdgeEndpoint_adj Q.claim67.M e.1 e.2
  fin_cases s <;> fin_cases t
  · exact False.elim (hst rfl)
  · simpa [richSlotVertex] using h01
  · simpa [richSlotVertex] using h01.symm
  · exact False.elim (hst rfl)

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
    (rootSide0 : K0 → Fin 2) (rootSide1 : K1 → Fin 2)
    (rootSideb : Kb → Fin 2)

private abbrev pairOrient :=
  canonicalCoordinateOrientation P S capacity0 capacity1 capacityb A
    rootSide0 rootSide1 rootSideb

private abbrev pairRootSlot :=
  coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
    (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A edge0 edge1
    edgeb (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
      rootSideb)

private abbrev pairInteriorSlot :=
  coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S capacity0
    capacity1 capacityb A edge0 edge1 edgeb
      (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
        rootSideb)

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
theorem canonicalDirectPair
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ e : K0, (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 e).1 (rootSide0 e)))
    (hroot1 : ∀ e : K1, (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge1 e).1 (rootSide1 e)))
    (hrootb : ∀ e : Kb, (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb e).1 (rootSideb e)))
    (i : SegmentIndex hT P (canonicalOptional P))
    (hparent : (AllocationHierarchy hT P (canonicalOptional P)).parent i =
      Sum.inl 0) :
    G.IsUniform rho
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (sourceSlot Pcluster Gdegree threshold quota R miss Q P))
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i)) ∧
      density ≤ G.edgeDensity
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (sourceSlot Pcluster Gdegree threshold quota R miss Q P))
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i)) := by
  apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho density H
  have hi : SegmentRootOriginal hT P (canonicalOptional P) i ∉ (∅ : Finset V) :=
    by simp
  rcases directSegment_sourceClass hT P (canonicalOptional P) i hparent with
        hcomponent | hbranch
  · obtain ⟨q, hclass, -⟩ := hcomponent
    rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
          rootSideb i = Sum.inl (componentReservoirSide P q) by
        exact coordinateHierarchyRootSlot_component hT P (canonicalOptional P)
          ∅ (sourceVertexReservoirSide P) S capacity0
          capacity1 capacityb A edge0 edge1 edgeb
          (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
            rootSideb) i q hi hclass]
    apply reserveVertices_adj_of_ne Pcluster Gdegree threshold quota R miss Q
    exact (directComponentReservoirSide_ne hT P (canonicalOptional P) i q
      hparent hclass).symm
  · obtain ⟨j, hclass, howner, _hroot⟩ := hbranch
    rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
          rootSideb i = coordinateBranchSlot P S capacity0 capacity1 capacityb A
            edge0 edge1 edgeb
              (pairOrient P S capacity0 capacity1 capacityb A rootSide0
                rootSide1 rootSideb) j 0 by
        change coordinateHierarchyRootSlot hT P (canonicalOptional P)
          ∅ (sourceVertexReservoirSide P) S capacity0
          capacity1 capacityb A edge0 edge1 edgeb
            (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
              rootSideb) i = _
        rw [coordinateHierarchyRootSlot_branch hT P (canonicalOptional P)
          ∅ (sourceVertexReservoirSide P) S capacity0
          capacity1 capacityb A edge0 edge1 edgeb
            (pairOrient P S capacity0 capacity1 capacityb A rootSide0
              rootSide1 rootSideb) i j hi hclass]
        congr 1
        exact segmentEndpointSide_root_zero_of_optionalParity hT P
          (canonicalOptional P) (canonicalOptional_parity hT P) i j hclass]
    rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j with
          hj | hj | hj
    · have hside := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
        P j (havailable (S.selected_available hj))
      rw [howner] at hside
      simp [sourceSlot, richSlotVertex, coordinateBranchSlot,
        coordinateBranchEdge, pairOrient, hj, hside]
      exact hroot0 (A.F0edge j)
    · have hside := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
        P j ((mem_majorResidualBranches P S j).mp hj).1
      rw [howner] at hside
      have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
      simp [sourceSlot, richSlotVertex, coordinateBranchSlot,
        coordinateBranchEdge, pairOrient, hj0, hj, hside]
      exact hroot1 (A.F1edge j)
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
      have horient := canonicalCoordinateOrientation_minor_zero P S capacity0
        capacity1 capacityb A rootSide0 rootSide1 rootSideb havailable j hj
      simp [sourceSlot, richSlotVertex, coordinateBranchSlot,
        coordinateBranchEdge, pairOrient, hj0, hj1, hside, horient]
      exact hrootb (A.Fbedge j)

/-- A component-root attachment is either an edge between the two root
reservoirs or the reverse of the source-facing root pair of its parent
branch. -/
theorem canonicalComponentAttachmentPair
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ e : K0, (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 e).1 (rootSide0 e)))
    (hroot1 : ∀ e : K1, (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge1 e).1 (rootSide1 e)))
    (hrootb : ∀ e : Kb, (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb e).1 (rootSideb e)))
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
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l b ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
              rootSide1 rootSideb l b)) k a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i)) ∧
      density ≤ G.edgeDensity
        (HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P (canonicalOptional P))
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l b ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
              rootSide1 rootSideb l b)) k a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i)) := by
  have haRoot := componentRoot_attachment_coordinate_eq_segmentRoot hT P
    (canonicalOptional P) (canonicalOptional_covers_cutParents P) i k a q hi
    hparent
  rw [HierarchicalSegmentForest.rawCandidate, if_pos haRoot]
  apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho density H
  have hiEmpty : SegmentRootOriginal hT P (canonicalOptional P) i ∉
      (∅ : Finset V) := by simp
  rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
        capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
        rootSideb i = Sum.inl (componentReservoirSide P q) by
      exact coordinateHierarchyRootSlot_component hT P (canonicalOptional P) ∅
        (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A edge0
        edge1 edgeb _ i q hiEmpty hi]
  cases hk : segmentSourceClass hT P (canonicalOptional P) k with
  | inl r =>
      have hkEmpty : SegmentRootOriginal hT P (canonicalOptional P) k ∉
          (∅ : Finset V) := by simp
      rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
            rootSideb k = Sum.inl (componentReservoirSide P r) by
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
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
            rootSideb k = coordinateBranchSlot P S capacity0 capacity1 capacityb
              A edge0 edge1 edgeb
                (pairOrient P S capacity0 capacity1 capacityb A rootSide0
                  rootSide1 rootSideb) j 0 by
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
        have horient := canonicalCoordinateOrientation_selected_zero P S
          capacity0 capacity1 capacityb A rootSide0 rootSide1 rootSideb j hj
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          pairOrient, hj, hside, horient] using (hroot0 (A.F0edge j)).symm
      · have howner := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
          P j ((mem_majorResidualBranches P S j).mp hj).1
        rw [howner] at hside
        have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
        have horient := canonicalCoordinateOrientation_residual_zero P S
          capacity0 capacity1 capacityb A rootSide0 rootSide1 rootSideb j hj
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          pairOrient, hj0, hj, hside, horient] using (hroot1 (A.F1edge j)).symm
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
        have horient := canonicalCoordinateOrientation_minor_zero P S capacity0
          capacity1 capacityb A rootSide0 rootSide1 rootSideb havailable j hj
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          pairOrient, hj0, hj1, hside, horient] using (hrootb (A.Fbedge j)).symm

/-- A branch segment is attached either to its owner component reservoir or
to the opposite endpoint of the same assigned matching edge. -/
theorem canonicalBranchAttachmentPair
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ e : K0, (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 e).1 (rootSide0 e)))
    (hroot1 : ∀ e : K1, (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge1 e).1 (rootSide1 e)))
    (hrootb : ∀ e : Kb, (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb e).1 (rootSideb e)))
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
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l b ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
              rootSide1 rootSideb l b)) k a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i)) ∧
      density ≤ G.edgeDensity
        (HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P (canonicalOptional P))
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l b ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
              rootSide1 rootSideb l b)) k a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i)) := by
  have hiEmpty : SegmentRootOriginal hT P (canonicalOptional P) i ∉
      (∅ : Finset V) := by simp
  have hrootSide := segmentEndpointSide_root_zero_of_optionalParity hT P
    (canonicalOptional P) (canonicalOptional_parity hT P) i j hi
  rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
        capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
        rootSideb i = coordinateBranchSlot P S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb
            (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
              rootSideb) j 0 by
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
          capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
          rootSideb k = Sum.inl
            (componentReservoirSide P ((branchForest P).owner j)) by
        exact coordinateHierarchyRootSlot_component hT P (canonicalOptional P)
          ∅ (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb _ k ((branchForest P).owner j) hkEmpty hkclass]
    apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho density H
    rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j with
        hj | hj | hj
    · have howner := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
        P j (havailable (S.selected_available hj))
      have horient := canonicalCoordinateOrientation_selected_zero P S
        capacity0 capacity1 capacityb A rootSide0 rootSide1 rootSideb j hj
      simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        pairOrient, hj, howner, horient] using hroot0 (A.F0edge j)
    · have howner := componentReservoirSide_owner_eq_zero_of_mem_halfBranches
        P j ((mem_majorResidualBranches P S j).mp hj).1
      have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
      have horient := canonicalCoordinateOrientation_residual_zero P S
        capacity0 capacity1 capacityb A rootSide0 rootSide1 rootSideb j hj
      simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        pairOrient, hj0, hj, howner, horient] using hroot1 (A.F1edge j)
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
      have horient := canonicalCoordinateOrientation_minor_zero P S capacity0
        capacity1 capacityb A rootSide0 rootSide1 rootSideb havailable j hj
      simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        pairOrient, hj0, hj1, howner, horient] using hrootb (A.Fbedge j)
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
          capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
          rootSideb k a = coordinateBranchSlot P S capacity0 capacity1 capacityb
            A edge0 edge1 edgeb
              (pairOrient P S capacity0 capacity1 capacityb A rootSide0
                rootSide1 rootSideb) j 1 by
        change coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb _ k a = _
        rw [coordinateHierarchyInteriorSlot_branch hT P (canonicalOptional P) S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb _ k j hlclass a,
          hside]]
    apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho density H
    have hne :
        (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
          rootSideb j) 1 ≠
        (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
          rootSideb j) 0 := by
      intro h
      exact one_ne_zero
        ((pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
          rootSideb j).injective h)
    rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j with
        hj | hj | hj
    · simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        pairOrient, hj] using matchingVertices_adj_of_ne Pcluster Gdegree
          threshold quota R miss Q (edge0 (A.F0edge j)) _ _ hne
    · have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
      simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
        pairOrient, hj0, hj] using matchingVertices_adj_of_ne Pcluster Gdegree
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
        pairOrient, hj0, hj1] using matchingVertices_adj_of_ne Pcluster Gdegree
          threshold quota R miss Q (edgeb (A.Fbedge j)) _ _ hne

/-- Every internal edge of a branch segment uses the two opposite endpoints
of that branch's assigned matching edge.  Component-root segments are
singletons, so they have no internal edge. -/
theorem canonicalInternalPair
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
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l c ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
              rootSide1 rootSideb l c)) i a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i b)) ∧
      density ≤ G.edgeDensity
        (HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P (canonicalOptional P))
          (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb)
          (slotWhole Pcluster Gdegree threshold quota R miss Q)
          (fun l c ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
            (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
              rootSide1 rootSideb l c)) i a)
        (slotWhole Pcluster Gdegree threshold quota R miss Q
          (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i b)) := by
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
        (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
          rootSideb j)
            (segmentEndpointSide hT P (canonicalOptional P) i j a) ≠
        (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
          rootSideb j)
            (segmentEndpointSide hT P (canonicalOptional P) i j b) := by
      intro heq
      exact hsideNe
        ((pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
          rootSideb j).injective heq)
    have hslotA := coordinateHierarchyInteriorSlot_branch hT P
      (canonicalOptional P) S capacity0 capacity1 capacityb A edge0 edge1 edgeb
      (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
        rootSideb) i j hiclass a
    have hslotB := coordinateHierarchyInteriorSlot_branch hT P
      (canonicalOptional P) S capacity0 capacity1 capacityb A edge0 edge1 edgeb
      (pairOrient P S capacity0 capacity1 capacityb A rootSide0 rootSide1
        rootSideb) i j hiclass b
    by_cases ha :
        a = (AllocationHierarchy hT P (canonicalOptional P)).segments.root i
    · have hrootSide := segmentEndpointSide_root_zero_of_optionalParity hT P
        (canonicalOptional P) (canonicalOptional_parity hT P) i j hiclass
      rw [HierarchicalSegmentForest.rawCandidate, if_pos ha]
      have hiEmpty : SegmentRootOriginal hT P (canonicalOptional P) i ∉
          (∅ : Finset V) := by simp
      rw [show pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i = coordinateBranchSlot P S capacity0
              capacity1 capacityb A edge0 edge1 edgeb
                (pairOrient P S capacity0 capacity1 capacityb A rootSide0
                  rootSide1 rootSideb) j 0 by
          change coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
            (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
            edge0 edge1 edgeb _ i = _
          rw [coordinateHierarchyRootSlot_branch hT P (canonicalOptional P) ∅
            (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
            edge0 edge1 edgeb _ i j hiEmpty hiclass]
          congr 1,
        show pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i b = coordinateBranchSlot P S capacity0
              capacity1 capacityb A edge0 edge1 edgeb
                (pairOrient P S capacity0 capacity1 capacityb A rootSide0
                  rootSide1 rootSideb) j
                    (segmentEndpointSide hT P (canonicalOptional P) i j b) by
          exact hslotB]
      apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho
        density H
      rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j
          with hj | hj | hj
      · simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          pairOrient, hj, ha, hrootSide] using
            matchingVertices_adj_of_ne Pcluster Gdegree threshold quota R miss Q
              (edge0 (A.F0edge j)) _ _ hphysicalNe
      · have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          pairOrient, hj0, hj, ha, hrootSide] using
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
          pairOrient, hj0, hj1, ha, hrootSide] using
            matchingVertices_adj_of_ne Pcluster Gdegree threshold quota R miss Q
              (edgeb (A.Fbedge j)) _ _ hphysicalNe
    · rw [HierarchicalSegmentForest.rawCandidate, if_neg ha,
        show pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i a = coordinateBranchSlot P S capacity0
              capacity1 capacityb A edge0 edge1 edgeb
                (pairOrient P S capacity0 capacity1 capacityb A rootSide0
                  rootSide1 rootSideb) j
                    (segmentEndpointSide hT P (canonicalOptional P) i j a) by
          exact hslotA,
        show pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0
            rootSide1 rootSideb i b = coordinateBranchSlot P S capacity0
              capacity1 capacityb A edge0 edge1 edgeb
                (pairOrient P S capacity0 capacity1 capacityb A rootSide0
                  rootSide1 rootSideb) j
                    (segmentEndpointSide hT P (canonicalOptional P) i j b) by
          exact hslotB]
      apply wholePair_of_adj Pcluster Gdegree threshold quota R miss Q G rho
        density H
      rcases branchClass_mem_selected_or_residual_or_minor' P S havailable j
          with hj | hj | hj
      · simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          pairOrient, hj] using matchingVertices_adj_of_ne Pcluster Gdegree
            threshold quota R miss Q (edge0 (A.F0edge j)) _ _ hphysicalNe
      · have hj0 := (mem_majorResidualBranches P S j).mp hj |>.2
        simpa [richSlotVertex, coordinateBranchSlot, coordinateBranchEdge,
          pairOrient, hj0, hj] using matchingVertices_adj_of_ne Pcluster Gdegree
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
          pairOrient, hj0, hj1] using matchingVertices_adj_of_ne Pcluster
            Gdegree threshold quota R miss Q (edgeb (A.Fbedge j)) _ _
              hphysicalNe

/-- The literal rich host supplies all six regular-pair obligations for the
canonical cut-parent segmentation with no distinguished branch vertices.
The only inputs are padded reduced-graph realization and the three genuine
source-facing adjacency rows. -/
theorem canonicalCoordinatePairFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ e : K0, (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 e).1 (rootSide0 e)))
    (hroot1 : ∀ e : K1, (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge1 e).1 (rootSide1 e)))
    (hrootb : ∀ e : Kb, (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb e).1 (rootSideb e))) :
    CoordinateHierarchyPairFacts
      (AllocationHierarchy hT P (canonicalOptional P)) G rho density
      (slotWhole Pcluster Gdegree threshold quota R miss Q
        (sourceSlot Pcluster Gdegree threshold quota R miss Q P))
      (pairRootSlot Pcluster Gdegree threshold quota R miss Q hT P S
        capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
        rootSideb)
      (slotWhole Pcluster Gdegree threshold quota R miss Q)
      (pairInteriorSlot Pcluster Gdegree threshold quota R miss Q hT P S
        capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
        rootSideb) := by
  refine
    { direct_uniform := fun i hp ↦ ?_
      direct_density := fun i hp ↦ ?_
      attach_uniform := fun i k a hp ↦ ?_
      attach_density := fun i k a hp ↦ ?_
      internal_uniform := fun i a b hab hb ↦ ?_
      internal_density := fun i a b hab hb ↦ ?_ }
  · exact (canonicalDirectPair Pcluster Gdegree threshold quota R miss Q hT P S
      capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
      rootSideb G rho density H havailable hroot0 hroot1 hrootb i hp).1
  · exact (canonicalDirectPair Pcluster Gdegree threshold quota R miss Q hT P S
      capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
      rootSideb G rho density H havailable hroot0 hroot1 hrootb i hp).2
  · cases hi : segmentSourceClass hT P (canonicalOptional P) i with
    | inl q =>
        exact (canonicalComponentAttachmentPair Pcluster Gdegree threshold quota
          R miss Q hT P S capacity0 capacity1 capacityb A edge0 edge1 edgeb
          rootSide0 rootSide1 rootSideb G rho density H havailable hroot0
          hroot1 hrootb i k a q hi hp).1
    | inr j =>
        exact (canonicalBranchAttachmentPair Pcluster Gdegree threshold quota R
          miss Q hT P S capacity0 capacity1 capacityb A edge0 edge1 edgeb
          rootSide0 rootSide1 rootSideb G rho density H havailable hroot0
          hroot1 hrootb i k a j hi hp).1
  · cases hi : segmentSourceClass hT P (canonicalOptional P) i with
    | inl q =>
        exact (canonicalComponentAttachmentPair Pcluster Gdegree threshold quota
          R miss Q hT P S capacity0 capacity1 capacityb A edge0 edge1 edgeb
          rootSide0 rootSide1 rootSideb G rho density H havailable hroot0
          hroot1 hrootb i k a q hi hp).2
    | inr j =>
        exact (canonicalBranchAttachmentPair Pcluster Gdegree threshold quota R
          miss Q hT P S capacity0 capacity1 capacityb A edge0 edge1 edgeb
          rootSide0 rootSide1 rootSideb G rho density H havailable hroot0
          hroot1 hrootb i k a j hi hp).2
  · exact (canonicalInternalPair Pcluster Gdegree threshold quota R miss Q hT P
      S capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
      rootSideb G rho density H havailable i a b hab hb).1
  · exact (canonicalInternalPair Pcluster Gdegree threshold quota R miss Q hT P
      S capacity0 capacity1 capacityb A edge0 edge1 edgeb rootSide0 rootSide1
      rootSideb G rho density H havailable i a b hab hb).2

end Source

end Erdos547b.ZhaoClaim615RichCoordinatePairFacts

#print axioms Erdos547b.ZhaoClaim615RichCoordinatePairFacts.canonicalDirectPair
#print axioms Erdos547b.ZhaoClaim615RichCoordinatePairFacts.canonicalCoordinatePairFacts
