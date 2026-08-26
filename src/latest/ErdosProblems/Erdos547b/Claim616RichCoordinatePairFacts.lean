/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateFacts
import ErdosProblems.Erdos547b.Claim616CoordinateCutParents

/-!
# Structural pair facts for the rich coordinate hierarchy

This file isolates the source-side facts needed to classify attachments in
the coordinate hierarchy.  A same-branch attachment never uses the root
coordinate of the earlier segment.  For a component-root attachment, marking
the recorded Zhao cut parents makes its parent coordinate literally a segment
root; the attachment then reduces to one of the existing distinguished,
selected, residual, or minor root pairs.  No cross-pair oracle is introduced.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinatePairFacts

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim68BranchGraphTransport
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateHostLayout
open Erdos547b.ZhaoClaim616CoordinateEdgeMaps
open Erdos547b.ZhaoClaim616CoordinateHostPairs
open Erdos547b.ZhaoClaim616CoordinateOrientation
open Erdos547b.ZhaoClaim616CoordinateSourceParity
open Erdos547b.ZhaoClaim616CoordinateCutAttachmentParity
open Erdos547b.ZhaoClaim616CoordinateCutParents
open Erdos547b.ZhaoClaim616RichCoordinateApplication
open Erdos547b.ZhaoClaim616RichCoordinateAllocation
open Erdos547b.ZhaoClaim616RichCoordinateFacts
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Adjacent component roots occupy opposite distinguished-reservoir sides. -/
private theorem componentReservoirSide_ne_of_adj
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (q r : Fin P.numParts) (hqr : T.Adj (P.roots q) (P.roots r)) :
    componentReservoirSide P q ≠ componentReservoirSide P r := by
  have hparity := TreePartition.rootParity_ne_of_adj hT globalRoot hqr
  unfold componentReservoirSide
  by_cases hq : T.dist globalRoot (P.roots q) % 2 = (majorParity P).val
  · by_cases hr : T.dist globalRoot (P.roots r) % 2 = (majorParity P).val
    · exact False.elim (hparity (hq.trans hr.symm))
    · simp [hq, hr]
  · by_cases hr : T.dist globalRoot (P.roots r) % 2 = (majorParity P).val
    · simp [hq, hr]
    · have hqLt := Nat.mod_lt (T.dist globalRoot (P.roots q)) (by omega : 0 < 2)
      have hrLt := Nat.mod_lt (T.dist globalRoot (P.roots r)) (by omega : 0 < 2)
      have hmLt := (majorParity P).isLt
      have hsame : T.dist globalRoot (P.roots q) % 2 =
          T.dist globalRoot (P.roots r) % 2 := by omega
      exact False.elim (hparity hsame)

/-- Symmetry of a whole regular pair, including its density lower bound. -/
private theorem richWholePair_symm {Host : Type*}
    (G : SimpleGraph Host) [DecidableRel G.Adj]
    (epsilon density : ℚ) {X Y : Finset Host}
    (hpair : G.IsUniform epsilon X Y ∧
      density ≤ G.edgeDensity X Y) :
    G.IsUniform epsilon Y X ∧ density ≤ G.edgeDensity Y X :=
  ⟨hpair.1.symm, by simpa [G.edgeDensity_comm] using hpair.2⟩

/-- Convert the rational regularity predicate carried by the reduced graph
back to the real predicate consumed by the hierarchy backend. -/
private theorem isUniform_real_of_rat {Host : Type*}
    {G : SimpleGraph Host} [DecidableRel G.Adj]
    {epsilon : ℚ} {X Y : Finset Host}
    (h : G.IsUniform epsilon X Y) : G.IsUniform (epsilon : ℝ) X Y := by
  intro X' hX' Y' hY' hXlarge hYlarge
  have hXlargeQ : (#X : ℚ) * epsilon ≤ (#X' : ℚ) := by
    exact_mod_cast hXlarge
  have hYlargeQ : (#Y : ℚ) * epsilon ≤ (#Y' : ℚ) := by
    exact_mod_cast hYlarge
  have hh := h hX' hY' hXlargeQ hYlargeQ
  exact_mod_cast hh

/-- An internal edge of a marked hierarchy segment is the corresponding
literal edge of the original tree. -/
theorem segmentInternal_original_adj
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional)
    (a b : Fin ((AllocationHierarchy hT P optional).segments.size i))
    (hab : ((AllocationHierarchy hT P optional).segments.tree i).Adj a b) :
    T.Adj
      (wholeHierarchyOriginalVertex T hT globalRoot
        (AllocationSpecial hT P optional) (Sum.inr ⟨i, a⟩))
      (wholeHierarchyOriginalVertex T hT globalRoot
        (AllocationSpecial hT P optional) (Sum.inr ⟨i, b⟩)) := by
  let F := wholeBranchForest T hT globalRoot
  let special := AllocationSpecial hT P optional
  let q : BranchVertex F := (markEnum F special i).1
  have hlocal : (F.branches.tree q.1).Adj
      (fiberEquiv F special i a).1 (fiberEquiv F special i b).1 := by
    change (((F.branches.tree q.1).induce (fiberSet F special q)).comap
      (fiberEquiv F special i)).Adj a b at hab
    exact hab
  have hforest : F.graph.Adj
      (Sum.inr (⟨q.1, (fiberEquiv F special i a).1⟩ : BranchVertex F))
      (Sum.inr (⟨q.1, (fiberEquiv F special i b).1⟩ : BranchVertex F)) := by
    rw [OrderedBranchForest.graph_adj_branch_branch]
    exact ⟨rfl, hlocal⟩
  have hordered :=
    (branchGraphIso (wholeOrderedTree T hT globalRoot)).toHom.map_rel hforest
  have horiginal := fromSingleCoordinate_map_adj hT hordered
  simpa [wholeHierarchyOriginalVertex, flatten, F, special, q] using horiginal

/-- If a branch-class segment is attached to an earlier segment of the same
branch class, then its attachment coordinate is an interior coordinate of
the earlier segment.  In particular, the selected case never asks for a
spurious `C--C` regular pair. -/
theorem sameBranchAttachment_parent_ne_segmentRoot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (i k : SegmentIndex hT P optional) (j : BranchIndex P)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size k))
    (hi : segmentSourceClass hT P optional i = Sum.inr j)
    (hk : segmentSourceClass hT P optional k = Sum.inr j)
    (hparent : (AllocationHierarchy hT P optional).parent i =
      Sum.inr ⟨k, a⟩) :
    a ≠ (AllocationHierarchy hT P optional).segments.root k := by
  intro ha
  have hparentSide := segmentParent_side_one_of_optionalParity
    hT P optional hparity i j hi
  have hcoordinateSide : segmentEndpointSide hT P optional k j a = 1 := by
    change canonicalBranchSide P j
        (wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P optional) (Sum.inr ⟨k, a⟩)) = 1
    rw [← hparent]
    exact hparentSide
  have hrootSide := segmentEndpointSide_root_zero_of_optionalParity
    hT P optional hparity k j hk
  rw [ha, hrootSide] at hcoordinateSide
  have := congrArg Fin.val hcoordinateSide
  omega

section ComponentAttachment

variable {B : Type v} {K : Type w}
variable [Fintype B] [DecidableEq B] [Fintype K] [DecidableEq K]
variable (G Gdegree : SimpleGraph B)
variable [DecidableRel G.Adj] [DecidableRel Gdegree.Adj]
variable (cluster : K → Finset B) (epsilon density : ℚ)
variable [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon density) L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (Aroot Broot : K) (C : Finset K) (rhoK : ℕ)
variable (Pcluster : ClusterAssignment B K) (threshold quota : ℕ)
variable
  (H : IndexedHostSystem G cluster epsilon density Aroot Broot C
    (MatchingDecomposition.Mout
      (R := regularityReducedGraph G cluster epsilon density) D)
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D)))
    rhoK Pcluster threshold quota Gdegree)
variable {target slack : ℕ}

private abbrev pairAllowed0 (i : Fin C.card) :=
  indexedAllowedEdges (regularityReducedGraph G cluster epsilon density)
    (MatchingDecomposition.Mout
      (R := regularityReducedGraph G cluster epsilon density) D).edgeSet.toFinite.toFinset
    matchingEdgeEndpoint C
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D))) i

private abbrev pairWhole :=
  slotWhole (G := G) (cluster := cluster) (epsilon := epsilon)
    (density := density) (A := Aroot) (Broot := Broot) (C := C)
    (C67 := C67)

private abbrev pairRootSlot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  coordinateHierarchyRootSlot hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (pairAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0
    Aalloc
    (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) orient

private abbrev pairInteriorSlot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  coordinateHierarchyInteriorSlot hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (pairAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0
    Aalloc
    (moutOriginalEdge (R := regularityReducedGraph G cluster epsilon density) D)
    (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) orient

private abbrev pairRootWhole
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)
    (i : SegmentIndex hT P optional) : Finset B :=
  pairWhole G cluster epsilon density Aroot Broot C
    (pairRootSlot G cluster epsilon density D C hT P optional S
      clusterCap base0 base1 baseb Aalloc orient i)

private abbrev pairInteriorWhole
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) : Finset B :=
  pairWhole G cluster epsilon density Aroot Broot C
    (pairInteriorSlot G cluster epsilon density D C hT P optional S
      clusterCap base0 base1 baseb Aalloc orient i a)

private abbrev pairRaw
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) : Finset B :=
  rawCandidate (AllocationHierarchy hT P optional)
    (pairRootSlot G cluster epsilon density D C hT P optional S
      clusterCap base0 base1 baseb Aalloc orient)
    (pairWhole G cluster epsilon density Aroot Broot C)
    (pairInteriorWhole G cluster epsilon density D Aroot Broot C hT P
      optional S clusterCap base0 base1 baseb Aalloc orient) i a

include H

/-- The stored distinguished pair, in the orientation selected by two
different reservoir-side tags. -/
private theorem richDistinguishedPair_of_ne
    (sourceSide targetSide : Fin 2) (hne : sourceSide ≠ targetSide) :
    G.IsUniform epsilon
        (pairWhole G cluster epsilon density Aroot Broot C
          (Sum.inl sourceSide : RootSlot (Fin C.card) (MatchingEdge C67.M)))
        (pairWhole G cluster epsilon density Aroot Broot C
          (Sum.inl targetSide : RootSlot (Fin C.card) (MatchingEdge C67.M))) ∧
      density ≤ G.edgeDensity
        (pairWhole G cluster epsilon density Aroot Broot C
          (Sum.inl sourceSide : RootSlot (Fin C.card) (MatchingEdge C67.M)))
        (pairWhole G cluster epsilon density Aroot Broot C
          (Sum.inl targetSide : RootSlot (Fin C.card) (MatchingEdge C67.M))) := by
  have hpair := distinguishedPair G cluster epsilon density D Aroot Broot C
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D)))
    rhoK Pcluster threshold quota Gdegree H
  fin_cases sourceSide <;> fin_cases targetSide
  · exact False.elim (hne rfl)
  · simpa [pairWhole, slotWhole] using hpair
  · exact ⟨hpair.1.symm, by
      simpa [pairWhole, slotWhole, G.edgeDensity_comm] using hpair.2⟩
  · exact False.elim (hne rfl)

/-- Once recorded cut parents are marked, every component-root attachment
uses one of the concrete rich root pairs.  In particular, its parent raw
candidate is a root pool, never an arbitrary matching-endpoint interior
pool. -/
theorem canonicalComponentRootAttachmentPair
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (hcut : cutParentVertices P ⊆ optional)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hV1Adj : ∀ x ∈ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Aroot x)
    (hMbAdj : ∀ e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Broot
          (matchingEdgeEndpoint e.1.1 (mbSide e)))
    (i k : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size k))
    (q : Fin P.numParts)
    (hi : segmentSourceClass hT P optional i = Sum.inl q)
    (hparent : (AllocationHierarchy hT P optional).parent i =
      Sum.inr ⟨k, a⟩) :
    let orient := canonicalCoordinateOrientation G cluster epsilon density D C
      hT P optional S clusterCap base0 base1 baseb Aalloc mbSide
    G.IsUniform epsilon
        (rawCandidate (AllocationHierarchy hT P optional)
          (pairRootSlot G cluster epsilon density D C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient)
          (pairWhole G cluster epsilon density Aroot Broot C)
          (fun l b ↦ pairWhole G cluster epsilon density Aroot Broot C
            (pairInteriorSlot G cluster epsilon density D C hT P optional S
              clusterCap base0 base1 baseb Aalloc orient l b)) k a)
        (pairWhole G cluster epsilon density Aroot Broot C
          (pairRootSlot G cluster epsilon density D C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient i)) ∧
      density ≤ G.edgeDensity
        (rawCandidate (AllocationHierarchy hT P optional)
          (pairRootSlot G cluster epsilon density D C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient)
          (pairWhole G cluster epsilon density Aroot Broot C)
          (fun l b ↦ pairWhole G cluster epsilon density Aroot Broot C
            (pairInteriorSlot G cluster epsilon density D C hT P optional S
              clusterCap base0 base1 baseb Aalloc orient l b)) k a)
        (pairWhole G cluster epsilon density Aroot Broot C
          (pairRootSlot G cluster epsilon density D C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient i)) := by
  dsimp only
  have haRoot := componentRoot_attachment_coordinate_eq_segmentRoot
    hT P optional hcut i k a q hi hparent
  generalize hkclass : segmentSourceClass hT P optional k = parentClass
  rcases parentClass with r | j
  · have hrootI : SegmentRootOriginal hT P optional i = P.roots q :=
      (literalSourceClass_eq_inl_iff P _ q).mp hi
    have hrootK : SegmentRootOriginal hT P optional k = P.roots r :=
      (literalSourceClass_eq_inl_iff P _ r).mp hkclass
    have hparentOriginal : SegmentParentOriginal hT P optional i =
        SegmentRootOriginal hT P optional k := by
      unfold SegmentParentOriginal SegmentRootOriginal
      rw [hparent, haRoot]
      rfl
    have hadj : T.Adj (P.roots r) (P.roots q) := by
      rw [← hrootK, ← hrootI, ← hparentOriginal,
        segmentParentOriginal_eq_treeParent]
      exact TreePartition.parent_adj hT globalRoot
        (segmentRootOriginal_ne_globalRoot hT P optional i)
    have hne := componentReservoirSide_ne_of_adj hT P r q hadj
    have hpair := richDistinguishedPair_of_ne G Gdegree cluster epsilon
      density D Aroot Broot C rhoK Pcluster threshold quota H
      (componentReservoirSide P r) (componentReservoirSide P q) hne
    simpa [rawCandidate, pairRootSlot, pairWhole,
      coordinateHierarchyRootSlot, hkclass, hi, haRoot] using hpair
  · rcases branchClass_mem_selected_or_residual_or_minor P S j with
        hj | hj | hj
    · have hside := componentRoot_cutAttachment_parity_selected
        hT P optional S i k a q j hi hparent hkclass hj
      have hrootSide := segmentEndpointSide_root_zero_of_optionalParity
        hT P optional hparity k j hkclass
      rw [haRoot, hrootSide] at hside
      have hsideZero : componentReservoirSide P q = 0 := by
        simpa [orientedSide] using hside
      have hpair := root_selectedPair G cluster epsilon density D Aroot Broot C
        (MatchingDecomposition.V2
            (R := regularityReducedGraph G cluster epsilon density) D ∩
          (matchingSupport (MatchingDecomposition.Mout
              (R := regularityReducedGraph G cluster epsilon density) D) \
            matchingSupport (MatchingDecomposition.Mb
              (R := regularityReducedGraph G cluster epsilon density) D)))
        rhoK Pcluster threshold quota Gdegree H (Aalloc.F0cluster j)
      have hpairSymm := richWholePair_symm
        (G := G) (epsilon := epsilon)
        (density := density) hpair
      simpa [rawCandidate, pairRootSlot, pairWhole, slotWhole, indexedCluster,
        coordinateHierarchyRootSlot, coordinateBranchRootSlot, hkclass, hi,
        haRoot, hj, hsideZero] using hpairSymm
    · have hside := componentRoot_cutAttachment_parity_majorResidual
        hT P optional S i k a q j hi hparent hkclass hj
      have hrootSide := segmentEndpointSide_root_zero_of_optionalParity
        hT P optional hparity k j hkclass
      rw [haRoot, hrootSide] at hside
      have hsideZero : componentReservoirSide P q = 0 := by
        simpa [orientedSide] using hside
      have hj0 : j ∉ S.selected := (mem_majorResidualBranches P S j).mp hj |>.2
      have hpair := canonicalResidualRootPair G cluster epsilon density D Aroot
        C hT P optional S clusterCap base0 base1 baseb Aalloc mbSide hV1Adj j hj
      have hpairSymm := richWholePair_symm
        (G := G) (epsilon := epsilon)
        (density := density) hpair
      simpa [rawCandidate, pairRootSlot, pairWhole, slotWhole, indexedCluster,
        coordinateHierarchyRootSlot, coordinateBranchRootSlot, hkclass, hi,
        haRoot, hj0, hj, hsideZero] using hpairSymm
    · have hside := componentRoot_cutAttachment_parity_minor
        hT P optional S i k a q j hi hparent hkclass hj
      have hrootSide := segmentEndpointSide_root_zero_of_optionalParity
        hT P optional hparity k j hkclass
      rw [haRoot, hrootSide] at hside
      have hsideOne : componentReservoirSide P q = 1 := by
        simpa [orientedSide] using hside
      have hjHalf : j ∉ halfBranches P := by
        intro hjHalf
        exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
          hjHalf hj
      have hj0 : j ∉ S.selected := fun hjSelected ↦
        hjHalf (S.selected_available hjSelected)
      have hj1 : j ∉ majorResidualBranches P S := by
        intro hjResidual
        exact hjHalf ((mem_majorResidualBranches P S j).mp hjResidual).1
      have hpair := canonicalMinorRootPair G cluster epsilon density D Broot C
        hT P optional S clusterCap base0 base1 baseb Aalloc mbSide hMbAdj j hj
      have hpairSymm := richWholePair_symm
        (G := G) (epsilon := epsilon)
        (density := density) hpair
      simpa [rawCandidate, pairRootSlot, pairWhole, slotWhole, indexedCluster,
        coordinateHierarchyRootSlot, coordinateBranchRootSlot, hkclass, hi,
        haRoot, hj0, hj1, hsideOne] using hpairSymm

/-- Every branch-root attachment uses either its owner reservoir (for the
canonical branch root) or the opposite endpoint of the same assigned
matching edge (for a later marked segment). -/
theorem canonicalBranchRootAttachmentPair
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hV1Adj : ∀ x ∈ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Aroot x)
    (hMbAdj : ∀ e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Broot
          (matchingEdgeEndpoint e.1.1 (mbSide e)))
    (i k : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size k))
    (j : BranchIndex P)
    (hi : segmentSourceClass hT P optional i = Sum.inr j)
    (hparent : (AllocationHierarchy hT P optional).parent i =
      Sum.inr ⟨k, a⟩) :
    let orient := canonicalCoordinateOrientation G cluster epsilon density D C
      hT P optional S clusterCap base0 base1 baseb Aalloc mbSide
    G.IsUniform epsilon
        (pairRaw G cluster epsilon density D Aroot Broot C hT P optional S
          clusterCap base0 base1 baseb Aalloc orient k a)
        (pairRootWhole G cluster epsilon density D Aroot Broot C hT P optional S
          clusterCap base0 base1 baseb Aalloc orient i) ∧
      density ≤ G.edgeDensity
        (pairRaw G cluster epsilon density D Aroot Broot C hT P optional S
          clusterCap base0 base1 baseb Aalloc orient k a)
        (pairRootWhole G cluster epsilon density D Aroot Broot C hT P optional S
          clusterCap base0 base1 baseb Aalloc orient i) := by
  dsimp only
  rcases segment_attachment_of_branch_class hT P optional i j hi with
      hcanonical | hlater
  · have hparentValue :
        wholeHierarchyOriginalVertex T hT globalRoot
            (AllocationSpecial hT P optional) (Sum.inr ⟨k, a⟩) =
          P.roots ((branchForest P).owner j) := by
      calc
        _ = SegmentParentOriginal hT P optional i := congrArg
          (wholeHierarchyOriginalVertex T hT globalRoot
            (AllocationSpecial hT P optional)) hparent.symm
        _ = _ := hcanonical.2
    have hkclass : segmentSourceClass hT P optional k =
        Sum.inl ((branchForest P).owner j) := by
      have hc := wholeSegment_sourceClass_eq_of_boundary hT P optional
        (canonicalWholeSourceBoundary hT P optional) k a
      have hrootClass : literalSourceClass P
          (P.roots ((branchForest P).owner j)) =
            Sum.inl ((branchForest P).owner j) :=
        (literalSourceClass_eq_inl_iff P _ _).mpr rfl
      rw [hparentValue, hrootClass] at hc
      exact hc.symm
    have hkRoot : k ∈ rootSegments hT P optional :=
      (mem_rootSegments_iff hT P optional k).mpr
        ⟨(branchForest P).owner j, hkclass⟩
    have hkSize := rootSegment_size_eq_one hT P optional k hkRoot
    have haRoot : a = (AllocationHierarchy hT P optional).segments.root k := by
      apply Fin.ext
      have haLt := a.isLt
      have hrLt := ((AllocationHierarchy hT P optional).segments.root k).isLt
      omega
    rcases branchClass_mem_selected_or_residual_or_minor P S j with
        hj | hj | hj
    · have hownerSide := componentReservoirSide_owner_eq_zero_of_mem_selected
        P S j hj
      have hpair := root_selectedPair G cluster epsilon density D Aroot Broot C
        (MatchingDecomposition.V2
            (R := regularityReducedGraph G cluster epsilon density) D ∩
          (matchingSupport (MatchingDecomposition.Mout
              (R := regularityReducedGraph G cluster epsilon density) D) \
            matchingSupport (MatchingDecomposition.Mb
              (R := regularityReducedGraph G cluster epsilon density) D)))
        rhoK Pcluster threshold quota Gdegree H (Aalloc.F0cluster j)
      simpa [pairRaw, pairRootWhole, rawCandidate, pairRootSlot, pairWhole,
        slotWhole, indexedCluster, coordinateHierarchyRootSlot,
        coordinateBranchRootSlot, hkclass, hi, haRoot, hj, hownerSide]
        using hpair
    · have hownerSide :=
        componentReservoirSide_owner_eq_zero_of_mem_majorResidual P S j hj
      have hj0 : j ∉ S.selected := (mem_majorResidualBranches P S j).mp hj |>.2
      have hpair := canonicalResidualRootPair G cluster epsilon density D Aroot
        C hT P optional S clusterCap base0 base1 baseb Aalloc mbSide hV1Adj j hj
      simpa [pairRaw, pairRootWhole, rawCandidate, pairRootSlot, pairWhole,
        slotWhole, coordinateHierarchyRootSlot, coordinateBranchRootSlot,
        hkclass, hi, haRoot, hj0, hj, hownerSide] using hpair
    · have hownerSide := componentReservoirSide_owner_eq_one_of_mem_minorBranches
        P j hj
      have hjHalf : j ∉ halfBranches P := by
        intro hjHalf
        exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
          hjHalf hj
      have hj0 : j ∉ S.selected := fun hjSelected ↦
        hjHalf (S.selected_available hjSelected)
      have hj1 : j ∉ majorResidualBranches P S := by
        intro hjResidual
        exact hjHalf ((mem_majorResidualBranches P S j).mp hjResidual).1
      have hpair := canonicalMinorRootPair G cluster epsilon density D Broot C
        hT P optional S clusterCap base0 base1 baseb Aalloc mbSide hMbAdj j hj
      simpa [pairRaw, pairRootWhole, rawCandidate, pairRootSlot, pairWhole,
        slotWhole, coordinateHierarchyRootSlot, coordinateBranchRootSlot,
        hkclass, hi, haRoot, hj0, hj1, hownerSide] using hpair
  · obtain ⟨l, b, hlparent, -, hlclass⟩ := hlater
    have hsigma : (⟨l, b⟩ : Σ m,
        Fin ((AllocationHierarchy hT P optional).segments.size m)) = ⟨k, a⟩ :=
      Sum.inr.inj (hlparent.symm.trans hparent)
    cases hsigma
    have haNe := sameBranchAttachment_parent_ne_segmentRoot
      hT P optional hparity i k j a hi hlclass hparent
    have hside : segmentEndpointSide hT P optional k j a = 1 := by
      change canonicalBranchSide P j
          (wholeHierarchyOriginalVertex T hT globalRoot
            (AllocationSpecial hT P optional) (Sum.inr ⟨k, a⟩)) = 1
      rw [← hparent]
      exact segmentParent_side_one_of_optionalParity
        hT P optional hparity i j hi
    have hinteriorSlot := coordinateHierarchyInteriorSlot_branch
      hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
      base0 Aalloc
      (moutOriginalEdge (R := regularityReducedGraph G cluster epsilon density) D)
      (fun e : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
      (fun e : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
      (canonicalCoordinateOrientation G cluster epsilon density D C hT P
        optional S clusterCap base0 base1 baseb Aalloc mbSide)
      k j hlclass a
    have hne :
        canonicalCoordinateOrientation G cluster epsilon density D C hT P
            optional S clusterCap base0 base1 baseb Aalloc mbSide j 1 ≠
          canonicalCoordinateOrientation G cluster epsilon density D C hT P
            optional S clusterCap base0 base1 baseb Aalloc mbSide j 0 := by
      intro heq
      exact one_ne_zero
        ((canonicalCoordinateOrientation G cluster epsilon density D C hT P
          optional S clusterCap base0 base1 baseb Aalloc mbSide j).injective heq)
    rcases branchClass_mem_selected_or_residual_or_minor P S j with
        hj | hj | hj
    · have hpair := canonicalSelectedAccessPair G Gdegree cluster epsilon
        density D Aroot Broot C rhoK Pcluster threshold quota H hT P optional S
        clusterCap base0 base1 baseb Aalloc mbSide j hj
      have hpairSymm := richWholePair_symm
        (G := G) (epsilon := epsilon) (density := density) hpair
      simpa [pairRaw, pairRootWhole, rawCandidate, pairRootSlot,
        pairInteriorWhole, pairInteriorSlot, pairWhole, slotWhole,
        indexedCluster, coordinateHierarchyRootSlot, coordinateBranchRootSlot,
        hinteriorSlot, hi, haNe, hside, hj]
        using hpairSymm
    · have hj0 : j ∉ S.selected := (mem_majorResidualBranches P S j).mp hj |>.2
      have hpair := originalMatchingPair_of_ne (C67 := C67) G cluster epsilon
        density (Aalloc.F1edge j).1
        (canonicalCoordinateOrientation G cluster epsilon density D C hT P
          optional S clusterCap base0 base1 baseb Aalloc mbSide j 1)
        (canonicalCoordinateOrientation G cluster epsilon density D C hT P
          optional S clusterCap base0 base1 baseb Aalloc mbSide j 0) hne
      simpa [pairRaw, pairRootWhole, rawCandidate, pairRootSlot,
        pairInteriorWhole, pairInteriorSlot, pairWhole, slotWhole,
        coordinateHierarchyRootSlot, coordinateBranchRootSlot,
        hinteriorSlot, hi, haNe, hside, hj0, hj]
        using hpair
    · have hjHalf : j ∉ halfBranches P := by
        intro hjHalf
        exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
          hjHalf hj
      have hj0 : j ∉ S.selected := fun hjSelected ↦
        hjHalf (S.selected_available hjSelected)
      have hj1 : j ∉ majorResidualBranches P S := by
        intro hjResidual
        exact hjHalf ((mem_majorResidualBranches P S j).mp hjResidual).1
      have hpair := originalMatchingPair_of_ne (C67 := C67) G cluster epsilon
        density (Aalloc.Fbedge j).1
        (canonicalCoordinateOrientation G cluster epsilon density D C hT P
          optional S clusterCap base0 base1 baseb Aalloc mbSide j 1)
        (canonicalCoordinateOrientation G cluster epsilon density D C hT P
          optional S clusterCap base0 base1 baseb Aalloc mbSide j 0) hne
      simpa [pairRaw, pairRootWhole, rawCandidate, pairRootSlot,
        pairInteriorWhole, pairInteriorSlot, pairWhole, slotWhole,
        coordinateHierarchyRootSlot, coordinateBranchRootSlot,
        hinteriorSlot, hi, haNe, hside, hj0, hj1]
        using hpair

/-- Every internal segment edge uses the selected access pair at the
selected root, and otherwise the two opposite endpoints of its one assigned
matching edge. -/
theorem canonicalInternalPair
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (i : SegmentIndex hT P optional)
    (a b : Fin ((AllocationHierarchy hT P optional).segments.size i))
    (hab : ((AllocationHierarchy hT P optional).segments.tree i).Adj a b)
    (hb : b ≠ (AllocationHierarchy hT P optional).segments.root i) :
    let orient := canonicalCoordinateOrientation G cluster epsilon density D C
      hT P optional S clusterCap base0 base1 baseb Aalloc mbSide
    G.IsUniform epsilon
        (pairRaw G cluster epsilon density D Aroot Broot C hT P optional S
          clusterCap base0 base1 baseb Aalloc orient i a)
        (pairInteriorWhole G cluster epsilon density D Aroot Broot C hT P
          optional S clusterCap base0 base1 baseb Aalloc orient i b) ∧
      density ≤ G.edgeDensity
        (pairRaw G cluster epsilon density D Aroot Broot C hT P optional S
          clusterCap base0 base1 baseb Aalloc orient i a)
        (pairInteriorWhole G cluster epsilon density D Aroot Broot C hT P
          optional S clusterCap base0 base1 baseb Aalloc orient i b) := by
  dsimp only
  generalize hiclass : segmentSourceClass hT P optional i = sourceClass
  rcases sourceClass with q | j
  · have hiRoot : i ∈ rootSegments hT P optional :=
      (mem_rootSegments_iff hT P optional i).mpr ⟨q, hiclass⟩
    have hiSize := rootSegment_size_eq_one hT P optional i hiRoot
    exfalso
    apply hb
    apply Fin.ext
    have hbLt := b.isLt
    have hrLt := ((AllocationHierarchy hT P optional).segments.root i).isLt
    omega
  · have horiginal := segmentInternal_original_adj hT P optional i a b hab
    have hsideNe : segmentEndpointSide hT P optional i j a ≠
        segmentEndpointSide hT P optional i j b :=
      canonicalBranchSide_ne_of_adj hT P j horiginal
    let orient := canonicalCoordinateOrientation G cluster epsilon density D C
      hT P optional S clusterCap base0 base1 baseb Aalloc mbSide
    have hphysicalNe : orient j (segmentEndpointSide hT P optional i j a) ≠
        orient j (segmentEndpointSide hT P optional i j b) := by
      intro heq
      exact hsideNe ((orient j).injective heq)
    have hslotA := coordinateHierarchyInteriorSlot_branch
      hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
      base0 Aalloc
      (moutOriginalEdge (R := regularityReducedGraph G cluster epsilon density) D)
      (fun e : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
      (fun e : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
      orient i j hiclass a
    have hslotB := coordinateHierarchyInteriorSlot_branch
      hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
      base0 Aalloc
      (moutOriginalEdge (R := regularityReducedGraph G cluster epsilon density) D)
      (fun e : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
      (fun e : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
      orient i j hiclass b
    rcases branchClass_mem_selected_or_residual_or_minor P S j with
        hj | hj | hj
    · by_cases ha : a = (AllocationHierarchy hT P optional).segments.root i
      · have hrootSide := segmentEndpointSide_root_zero_of_optionalParity
          hT P optional hparity i j hiclass
        rw [ha, hrootSide] at hsideNe
        have hbSide : segmentEndpointSide hT P optional i j b = 1 := by
          apply Fin.ext
          have hlt := (segmentEndpointSide hT P optional i j b).isLt
          have hnzero : (segmentEndpointSide hT P optional i j b).val ≠ 0 := by
            intro hz
            apply hsideNe
            exact (Fin.ext hz).symm
          omega
        have hpair := canonicalSelectedAccessPair G Gdegree cluster epsilon
          density D Aroot Broot C rhoK Pcluster threshold quota H hT P optional S
          clusterCap base0 base1 baseb Aalloc mbSide j hj
        simpa [pairRaw, pairRootWhole, rawCandidate, pairRootSlot,
          pairInteriorWhole, pairInteriorSlot, pairWhole, slotWhole,
          indexedCluster, coordinateHierarchyRootSlot, coordinateBranchRootSlot,
          hslotB, hiclass, ha, hj, hbSide] using hpair
      · have hpair := originalMatchingPair_of_ne (C67 := C67) G cluster
          epsilon density
          (moutOriginalEdge
            (R := regularityReducedGraph G cluster epsilon density) D
            (Aalloc.F0edge j))
          (orient j (segmentEndpointSide hT P optional i j a))
          (orient j (segmentEndpointSide hT P optional i j b)) hphysicalNe
        simpa [pairRaw, rawCandidate, pairInteriorWhole, pairInteriorSlot,
          pairWhole, slotWhole, hslotA, hslotB, hiclass, ha, hj, orient]
          using hpair
    · have hj0 : j ∉ S.selected := (mem_majorResidualBranches P S j).mp hj |>.2
      have hpair := originalMatchingPair_of_ne (C67 := C67) G cluster epsilon
        density (Aalloc.F1edge j).1
        (orient j (segmentEndpointSide hT P optional i j a))
        (orient j (segmentEndpointSide hT P optional i j b)) hphysicalNe
      by_cases ha : a = (AllocationHierarchy hT P optional).segments.root i
      · have hrootSide := segmentEndpointSide_root_zero_of_optionalParity
          hT P optional hparity i j hiclass
        simpa [pairRaw, rawCandidate, pairRootSlot, pairInteriorWhole,
          pairInteriorSlot, pairWhole, slotWhole, coordinateHierarchyRootSlot,
          coordinateBranchRootSlot, hslotB, hiclass, hj0, hj, ha, hrootSide,
          orient] using hpair
      · simpa [pairRaw, rawCandidate, pairRootSlot, pairInteriorWhole,
          pairInteriorSlot, pairWhole, slotWhole, coordinateHierarchyRootSlot,
          coordinateBranchRootSlot, hslotA, hslotB, hiclass, hj0, hj, ha,
          orient] using hpair
    · have hjHalf : j ∉ halfBranches P := by
        intro hjHalf
        exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
          hjHalf hj
      have hj0 : j ∉ S.selected := fun hjSelected ↦
        hjHalf (S.selected_available hjSelected)
      have hj1 : j ∉ majorResidualBranches P S := by
        intro hjResidual
        exact hjHalf ((mem_majorResidualBranches P S j).mp hjResidual).1
      have hpair := originalMatchingPair_of_ne (C67 := C67) G cluster epsilon
        density (Aalloc.Fbedge j).1
        (orient j (segmentEndpointSide hT P optional i j a))
        (orient j (segmentEndpointSide hT P optional i j b)) hphysicalNe
      by_cases ha : a = (AllocationHierarchy hT P optional).segments.root i
      · have hrootSide := segmentEndpointSide_root_zero_of_optionalParity
          hT P optional hparity i j hiclass
        simpa [pairRaw, rawCandidate, pairRootSlot, pairInteriorWhole,
          pairInteriorSlot, pairWhole, slotWhole, coordinateHierarchyRootSlot,
          coordinateBranchRootSlot, hslotB, hiclass, hj0, hj1, ha, hrootSide,
          orient] using hpair
      · simpa [pairRaw, rawCandidate, pairRootSlot, pairInteriorWhole,
          pairInteriorSlot, pairWhole, slotWhole, coordinateHierarchyRootSlot,
          coordinateBranchRootSlot, hslotA, hslotB, hiclass, hj0, hj1, ha,
          orient] using hpair

/-- The concrete rich host supplies all six pair obligations of the
coordinate hierarchy once the recorded cut parents are marked.  This is the
literal fact package consumed by `isContained_of_richCoordinateHostFacts`;
it contains no embedding or continuation premise. -/
theorem canonicalCoordinatePairFacts
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (hcut : cutParentVertices P ⊆ optional)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (pairAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hV1Adj : ∀ x ∈ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Aroot x)
    (hMbAdj : ∀ e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Broot
          (matchingEdgeEndpoint e.1.1 (mbSide e))) :
    let orient := canonicalCoordinateOrientation G cluster epsilon density D C
      hT P optional S clusterCap base0 base1 baseb Aalloc mbSide
    CoordinatePairFacts (AllocationHierarchy hT P optional) G epsilon density
      (pairWhole G cluster epsilon density Aroot Broot C
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
          RootSlot (Fin C.card) (MatchingEdge C67.M)))
      (pairRootSlot G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient)
      (pairWhole G cluster epsilon density Aroot Broot C)
      (pairInteriorWhole G cluster epsilon density D Aroot Broot C hT P
        optional S clusterCap base0 base1 baseb Aalloc orient) := by
  dsimp only
  let orient := canonicalCoordinateOrientation G cluster epsilon density D C
    hT P optional S clusterCap base0 base1 baseb Aalloc mbSide
  have hdirect : ∀ i,
      (AllocationHierarchy hT P optional).parent i = Sum.inl 0 →
      G.IsUniform epsilon
          (pairWhole G cluster epsilon density Aroot Broot C
            (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M)))
          (pairRootWhole G cluster epsilon density D Aroot Broot C hT P
            optional S clusterCap base0 base1 baseb Aalloc orient i) ∧
        density ≤ G.edgeDensity
          (pairWhole G cluster epsilon density Aroot Broot C
            (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M)))
          (pairRootWhole G cluster epsilon density D Aroot Broot C hT P
            optional S clusterCap base0 base1 baseb Aalloc orient i) := by
    intro i hparent
    simpa [orient, pairRootWhole, pairRootSlot, pairWhole] using
      (canonicalDirectPair G Gdegree cluster epsilon density D Aroot Broot C
        rhoK Pcluster threshold quota H hT P optional S clusterCap base0 base1
        baseb Aalloc mbSide hV1Adj hMbAdj i hparent)
  have hattach : ∀ i k a,
      (AllocationHierarchy hT P optional).parent i = Sum.inr ⟨k, a⟩ →
      G.IsUniform epsilon
          (pairRaw G cluster epsilon density D Aroot Broot C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient k a)
          (pairRootWhole G cluster epsilon density D Aroot Broot C hT P
            optional S clusterCap base0 base1 baseb Aalloc orient i) ∧
        density ≤ G.edgeDensity
          (pairRaw G cluster epsilon density D Aroot Broot C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient k a)
          (pairRootWhole G cluster epsilon density D Aroot Broot C hT P
            optional S clusterCap base0 base1 baseb Aalloc orient i) := by
    intro i k a hparent
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        simpa [orient] using
          (canonicalComponentRootAttachmentPair G Gdegree cluster epsilon
            density D Aroot Broot C rhoK Pcluster threshold quota H hT P
            optional hparity hcut S clusterCap base0 base1 baseb Aalloc mbSide
            hV1Adj hMbAdj i k a q hclass hparent)
    | inr j =>
        simpa [orient] using
          (canonicalBranchRootAttachmentPair G Gdegree cluster epsilon density
            D Aroot Broot C rhoK Pcluster threshold quota H hT P optional
            hparity S clusterCap base0 base1 baseb Aalloc mbSide hV1Adj hMbAdj
            i k a j hclass hparent)
  have hinternal : ∀ i a b,
      ((AllocationHierarchy hT P optional).segments.tree i).Adj a b →
      b ≠ (AllocationHierarchy hT P optional).segments.root i →
      G.IsUniform epsilon
          (pairRaw G cluster epsilon density D Aroot Broot C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient i a)
          (pairInteriorWhole G cluster epsilon density D Aroot Broot C hT P
            optional S clusterCap base0 base1 baseb Aalloc orient i b) ∧
        density ≤ G.edgeDensity
          (pairRaw G cluster epsilon density D Aroot Broot C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient i a)
          (pairInteriorWhole G cluster epsilon density D Aroot Broot C hT P
            optional S clusterCap base0 base1 baseb Aalloc orient i b) := by
    intro i a b hab hb
    simpa [orient] using
      (canonicalInternalPair G Gdegree cluster epsilon density D Aroot Broot C
        rhoK Pcluster threshold quota H hT P optional hparity S clusterCap
        base0 base1 baseb Aalloc mbSide i a b hab hb)
  refine
    { directUniform := fun i hp ↦ ?_
      directDensity := fun i hp ↦ ?_
      attachUniform := fun i k a hp ↦ ?_
      attachDensity := fun i k a hp ↦ ?_
      internalUniform := fun i a b hab hb ↦ ?_
      internalDensity := fun i a b hab hb ↦ ?_ }
  · simpa only [orient, pairRootWhole] using
      isUniform_real_of_rat (hdirect i hp).1
  · exact_mod_cast (hdirect i hp).2
  · simpa only [orient, pairRootWhole, pairRaw] using
      isUniform_real_of_rat (hattach i k a hp).1
  · exact_mod_cast (hattach i k a hp).2
  · simpa only [orient, pairRaw] using
      isUniform_real_of_rat (hinternal i a b hab hb).1
  · exact_mod_cast (hinternal i a b hab hb).2

end ComponentAttachment

end Erdos547b.ZhaoClaim616RichCoordinatePairFacts

#print axioms Erdos547b.ZhaoClaim616RichCoordinatePairFacts.sameBranchAttachment_parent_ne_segmentRoot
#print axioms Erdos547b.ZhaoClaim616RichCoordinatePairFacts.segmentInternal_original_adj
#print axioms Erdos547b.ZhaoClaim616RichCoordinatePairFacts.canonicalComponentRootAttachmentPair
#print axioms Erdos547b.ZhaoClaim616RichCoordinatePairFacts.canonicalBranchRootAttachmentPair
#print axioms Erdos547b.ZhaoClaim616RichCoordinatePairFacts.canonicalInternalPair
#print axioms Erdos547b.ZhaoClaim616RichCoordinatePairFacts.canonicalCoordinatePairFacts
