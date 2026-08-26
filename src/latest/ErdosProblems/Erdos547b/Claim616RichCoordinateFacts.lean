/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateApplication
import ErdosProblems.Erdos547b.Claim616HierarchyCoordinatePoolLoad
import ErdosProblems.Erdos547b.Claim616CoordinateSourceParity
import ErdosProblems.Erdos547b.Claim616CoordinateF0Load
import ErdosProblems.Erdos547b.Claim616CoordinateRootLoad

/-!
# Concrete fact packages for the rich Claim 6.16 coordinate application

This module constructs the compact proof-data records consumed by
`isContained_of_richCoordinateHostFacts`.  It contains no copy, embedding,
continuation, or cut-forest-data premise.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateFacts

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616RichCoordinateApplication
open Erdos547b.ZhaoClaim616HierarchicalCoordinateHostLayout
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim616CoordinateEdgeMaps
open Erdos547b.ZhaoClaim616RichCoordinateAllocation
open Erdos547b.ZhaoClaim616CoordinateSlotRelevance
open Erdos547b.ZhaoClaim616HierarchicalCoordinateEmbedding
open Erdos547b.ZhaoClaim616HierarchyCoordinatePoolLoad
open Erdos547b.ZhaoClaim616CoordinateHostPairs
open Erdos547b.ZhaoClaim616CoordinateOrientation
open Erdos547b.ZhaoClaim616CoordinateSourceParity
open Erdos547b.ZhaoClaim616CoordinateF0Load
open Erdos547b.ZhaoClaim616CoordinateRootLoad
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest

universe u v

variable {B : Type u} {K : Type v}
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

include H

/-- The current indexed host system supplies the exact separation record used
by the coordinate application.  This is only a repackaging of the concrete
raw-reservoir theorem from `Claim616HierarchicalCoordinateHostLayout`. -/
theorem coordinateSeparationFacts_of_indexedHostSystem
    (hCV1 : C ⊆ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D) :
    CoordinateSeparationFacts
      (slotRaw (G := G) (cluster := cluster) (epsilon := epsilon)
        (density := density) (C := C) (C67 := C67)
        H.rootReserve H.companionReserve)
      (RelevantSlot (G := G) (cluster := cluster) (epsilon := epsilon)
        (density := density) (D := D) (C := C)) := by
  refine ⟨?_⟩
  intro x y hx hy hxy
  exact slotRaw_disjoint_of_relevant_of_ne G cluster epsilon density D
    Aroot Broot C rhoK Pcluster threshold quota Gdegree H
    hCV1 x y hx hy hxy

omit H

/-- Removing two exact-size distinguished reserves from a host set loses at
most `2 * quota` vertices. -/
private theorem card_le_removeRootReserves_card_add_two_mul
    (rootReserve companionReserve X : Finset B)
    (hroot : rootReserve.card = quota)
    (hcompanion : companionReserve.card = quota) :
    X.card ≤
      (X \ (rootReserve ∪ companionReserve)).card + 2 * quota := by
  have hsplit := Finset.card_sdiff_add_card_inter X
    (rootReserve ∪ companionReserve)
  have hinter : #(X ∩ (rootReserve ∪ companionReserve)) ≤
      #(rootReserve ∪ companionReserve) :=
    Finset.card_le_card Finset.inter_subset_right
  have hunion : #(rootReserve ∪ companionReserve) ≤
      rootReserve.card + companionReserve.card := Finset.card_union_le _ _
  omega

/-- The exact natural loss bound plus the regularity-scale slack gives the
large-raw-reservoir inequality needed by the online embedding backend. -/
private theorem epsilon_mul_card_le_removeRootReserves_card
    (rootReserve companionReserve X : Finset B)
    (hroot : rootReserve.card = quota)
    (hcompanion : companionReserve.card = quota)
    (hslack : (epsilon : ℝ) * #X + (2 * quota : ℕ) ≤ #X) :
    (epsilon : ℝ) * #X ≤
      #(X \ (rootReserve ∪ companionReserve)) := by
  have hcardNat := card_le_removeRootReserves_card_add_two_mul
    (quota := quota) rootReserve companionReserve X hroot hcompanion
  have hcard : (#X : ℝ) ≤
      #(X \ (rootReserve ∪ companionReserve)) + (2 * quota : ℕ) := by
    exact_mod_cast hcardNat
  linarith

include H

/-- Every literal coordinate slot has a sufficiently large raw reservoir.
The three premises are exactly the two distinguished-reserve inequalities and
the loss-of-two-reserves inequality for ordinary clusters. -/
theorem richSlotRaw_large
    (hrootLarge : (epsilon : ℝ) * #(cluster Aroot) ≤ quota)
    (hcompanionLarge : (epsilon : ℝ) * #(cluster Broot) ≤ quota)
    (hclusterLarge : ∀ x,
      (epsilon : ℝ) * #(cluster x) + (2 * quota : ℕ) ≤ #(cluster x))
    (slot : Erdos547b.ZhaoClaim616HierarchicalSourceLayout.RootSlot
      (Fin C.card) (MatchingEdge C67.M)) :
    (epsilon : ℝ) *
        #(slotWhole (G := G) (cluster := cluster) (epsilon := epsilon)
          (density := density) (A := Aroot) (Broot := Broot)
          (C := C) (C67 := C67) slot) ≤
      #(slotRaw (G := G) (cluster := cluster) (epsilon := epsilon)
        (density := density) (C := C) (C67 := C67)
        H.rootReserve H.companionReserve slot) := by
  rcases slot with side | selected_or_edge
  · fin_cases side
    · simpa [slotWhole, slotRaw, H.rootReserve_card] using hrootLarge
    · simpa [slotWhole, slotRaw, H.companionReserve_card] using
        hcompanionLarge
  · rcases selected_or_edge with i | edge
    · simpa [slotWhole, slotRaw, removeRootReserves, indexedCluster] using
        (epsilon_mul_card_le_removeRootReserves_card
          (epsilon := epsilon) (quota := quota) H.rootReserve
          H.companionReserve (indexedCluster cluster C i)
          H.rootReserve_card H.companionReserve_card
          (by simpa [indexedCluster] using hclusterLarge (finsetValue C i)))
    · rcases edge with ⟨e, side⟩
      simpa [slotWhole, slotRaw, removeRootReserves] using
        (epsilon_mul_card_le_removeRootReserves_card
          (epsilon := epsilon) (quota := quota) H.rootReserve
          H.companionReserve (cluster (matchingEdgeEndpoint e.1 side))
          H.rootReserve_card H.companionReserve_card
          (hclusterLarge (matchingEdgeEndpoint e.1 side)))

omit H

section Capacity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

private theorem capacityMargin_mono
    (load bound small : ℕ) (removal rhs : ℝ)
    (hload : load ≤ bound)
    (hmargin : (bound + small + 1 : ℝ) + removal + 1 ≤ rhs) :
    (load + small + 1 : ℝ) + removal + 1 ≤ rhs := by
  have hloadReal : (load : ℝ) ≤ bound := by exact_mod_cast hload
  linarith

private abbrev factsAllowed0 (i : Fin C.card) :=
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

private abbrev factsWhole :=
  slotWhole (G := G) (cluster := cluster) (epsilon := epsilon)
    (density := density) (A := Aroot) (Broot := Broot) (C := C)
    (C67 := C67)

private abbrev factsRaw (rootReserve companionReserve : Finset B) :=
  slotRaw (G := G) (cluster := cluster) (epsilon := epsilon)
    (density := density) (C := C) (C67 := C67)
    rootReserve companionReserve

private abbrev factsRootSlot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  coordinateHierarchyRootSlot hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (factsAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0
    Aalloc
    (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) orient

private abbrev factsInteriorSlot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  coordinateHierarchyInteriorSlot hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (factsAllowed0 G cluster epsilon density D C)
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

private abbrev factsCapacity
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  exactCoordinateCapacity hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (factsAllowed0 G cluster epsilon density D C)
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

/-! ## Literal edge-map separation and endpoint loads -/

private theorem factsEdge0_injective :
    Function.Injective
      (moutOriginalEdge
        (R := regularityReducedGraph G cluster epsilon density) D) :=
  moutOriginalEdge_injective D

private theorem factsEdge1_injective :
    Function.Injective
      (fun e : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1) := by
  intro e f hef
  exact Subtype.ext hef

private theorem factsEdgeb_injective :
    Function.Injective
      (fun e : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) := by
  intro e f hef
  exact Subtype.ext hef

/-- The accessible `M_out` edges and residual `M_1` edges are literal
disjoint families: the former lie outside `minEdges`, while the latter lie
inside it. -/
private theorem factsEdge0_disjoint_edge1 :
    Disjoint
      (Finset.univ.image
        (moutOriginalEdge
          (R := regularityReducedGraph G cluster epsilon density) D))
      (Finset.univ.image
        (fun e : RemainingMinEdge
          (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)) := by
  rw [Finset.disjoint_left]
  intro e he0 he1
  obtain ⟨e0, -, he0eq⟩ := Finset.mem_image.mp he0
  obtain ⟨e1, -, he1eq⟩ := Finset.mem_image.mp he1
  have heq : (moutOriginalEdge
      (R := regularityReducedGraph G cluster epsilon density) D e0) = e1.1 :=
    he0eq.trans he1eq.symm
  have hout := moutOriginalEdge_mem
    (R := regularityReducedGraph G cluster epsilon density) D e0
  have hin : e1.1 ∈ D.minEdges :=
    (Finset.mem_sdiff.mp e1.2).1
  exact (Finset.mem_sdiff.mp hout).2 (heq.symm ▸ hin)

/-- The residual `M_1` and reserved `M_b` edge families are literal
disjoint families, on opposite sides of `minEdges`. -/
private theorem factsEdge1_disjoint_edgeb :
    Disjoint
      (Finset.univ.image
        (fun e : RemainingMinEdge
          (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1))
      (Finset.univ.image
        (fun e : ReservedEdge
          (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)) := by
  rw [Finset.disjoint_left]
  intro e he1 heb
  obtain ⟨e1, -, he1eq⟩ := Finset.mem_image.mp he1
  obtain ⟨eb, -, hebeq⟩ := Finset.mem_image.mp heb
  have heq : e1.1 = eb.1 := he1eq.trans hebeq.symm
  have hin : e1.1 ∈ D.minEdges :=
    (Finset.mem_sdiff.mp e1.2).1
  have hout := MatchingDecomposition.mb_subset
    (R := regularityReducedGraph G cluster epsilon density) D eb.2
  exact (Finset.mem_sdiff.mp hout).2 (heq ▸ hin)

/-- An actually assigned accessible `M_out` edge cannot be an `M_b` edge.
The proof uses the endpoint selected by `indexedAccessSide`, which belongs to
`V_2 ∩ (V(M_out) \ V(M_b))`; this is the exact assigned-only separation
required by the coordinate load theorem. -/
private theorem factsAssignedEdge0_ne_edgeb
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0) :
    ∀ j ∈ S.selected, ∀ eb : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D,
      moutOriginalEdge
          (R := regularityReducedGraph G cluster epsilon density) D
          (Aalloc.F0edge j) ≠ eb.1 := by
  intro j hj eb heq
  let side := indexedAccessSide
    (regularityReducedGraph G cluster epsilon density)
    (MatchingDecomposition.Mout
      (R := regularityReducedGraph G cluster epsilon density) D).edgeSet.toFinite.toFinset
    matchingEdgeEndpoint C
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D)))
    (Aalloc.F0cluster j) (Aalloc.F0edge j)
  have hspec := indexedAccessSide_spec
    (regularityReducedGraph G cluster epsilon density)
    (MatchingDecomposition.Mout
      (R := regularityReducedGraph G cluster epsilon density) D).edgeSet.toFinite.toFinset
    matchingEdgeEndpoint C
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D)))
    (Aalloc.F0cluster j) (Aalloc.F0edge j) (Aalloc.F0_allowed j hj)
  have hnotMb : matchingEdgeEndpoint
      (moutOriginalEdge
        (R := regularityReducedGraph G cluster epsilon density) D
        (Aalloc.F0edge j)).1
      (orientedSide side 1) ∉
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D) := by
    have hw := (Finset.mem_inter.mp hspec.1).2
    have hw' : matchingEdgeEndpoint
        (moutOriginalEdge
          (R := regularityReducedGraph G cluster epsilon density) D
          (Aalloc.F0edge j)).1
        (orientedSide side 1) ∈
          matchingSupport (MatchingDecomposition.Mout
            (R := regularityReducedGraph G cluster epsilon density) D) \
            matchingSupport (MatchingDecomposition.Mb
              (R := regularityReducedGraph G cluster epsilon density) D) := by
      by_cases hs : side = 0
      · simpa [side, orientedSide, hs, moutOriginalEdge_val] using hw
      · have hsOne : side = 1 := by
          apply Fin.ext
          have hlt := side.isLt
          have hnzero : side.val ≠ 0 := by
            intro hz
            apply hs
            apply Fin.ext
            simpa using hz
          omega
        simpa [side, orientedSide, hs, hsOne, moutOriginalEdge_val] using hw
    exact (Finset.mem_sdiff.mp hw').2
  apply hnotMb
  rw [heq]
  exact matchingEndpoint_mem_edgeFinsetSupport (G := G)
    (cluster := cluster) (epsilon := epsilon) (density := density)
    (C67 := C67) (L := L)
    (S := MatchingDecomposition.mbEdges
      (R := regularityReducedGraph G cluster epsilon density) D)
    (e := eb.1) eb.2 (orientedSide side 1)

/-- Actual coordinate occupancy of an assigned accessible `M_out` endpoint
is bounded by the corresponding selected-branch colour-class load.  All
edge-map injectivity and separation facts are derived from the literal
decomposition and the indexed-access condition. -/
theorem richCoordinatePoolLoad_edge0_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)
    (e : Fin (MatchingDecomposition.Mout
      (R := regularityReducedGraph G cluster epsilon density) D).edgeSet.toFinite.toFinset.card)
    (heAssigned : ∃ j ∈ S.selected, Aalloc.F0edge j = e)
    (c : Fin 2) :
    factsCapacity G cluster epsilon density D C hT P optional S clusterCap
        base0 base1 baseb Aalloc orient
        (Sum.inr (Sum.inr ⟨moutOriginalEdge
          (R := regularityReducedGraph G cluster epsilon density) D e, c⟩) :
          RootSlot (Fin C.card) (MatchingEdge C67.M)) ≤
      ∑ j ∈ S.selected.filter (Aalloc.F0edge · = e),
        Erdos547b.ZhaoLemma58GroupedSmallForest.orientedClassSize
          (branchForest P).branches orient j c := by
  exact coordinatePoolLoad_edge0_le hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (factsAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0
    Aalloc
    (moutOriginalEdge
      (R := regularityReducedGraph G cluster epsilon density) D)
    (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
    orient (factsEdge0_injective G cluster epsilon density D)
    (factsEdge0_disjoint_edge1 G cluster epsilon density D C)
    (factsAssignedEdge0_ne_edgeb G cluster epsilon density D C hT P optional
      S clusterCap base0 base1 baseb Aalloc)
    e heAssigned c

/-- Actual coordinate occupancy of an `M_1` endpoint is bounded by the
corresponding residual-branch colour-class load. -/
theorem richCoordinatePoolLoad_edge1_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)
    (e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C)
    (c : Fin 2) :
    factsCapacity G cluster epsilon density D C hT P optional S clusterCap
        base0 base1 baseb Aalloc orient
        (Sum.inr (Sum.inr ⟨e.1, c⟩) :
          RootSlot (Fin C.card) (MatchingEdge C67.M)) ≤
      ∑ j ∈ (majorResidualBranches P S).filter (Aalloc.F1edge · = e),
        Erdos547b.ZhaoLemma58GroupedSmallForest.orientedClassSize
          (branchForest P).branches orient j c := by
  exact coordinatePoolLoad_edge1_le hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (factsAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0
    Aalloc
    (moutOriginalEdge
      (R := regularityReducedGraph G cluster epsilon density) D)
    (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
    orient hparity (factsEdge1_injective G cluster epsilon density D C)
    (factsEdge0_disjoint_edge1 G cluster epsilon density D C)
    (factsEdge1_disjoint_edgeb G cluster epsilon density D C) e c

/-- Actual coordinate occupancy of an `M_b` endpoint is bounded by the
corresponding minor-branch colour-class load. -/
theorem richCoordinatePoolLoad_edgeb_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (hparity : OptionalBranchRootParity P optional)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)
    (e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D)
    (c : Fin 2) :
    factsCapacity G cluster epsilon density D C hT P optional S clusterCap
        base0 base1 baseb Aalloc orient
        (Sum.inr (Sum.inr ⟨e.1, c⟩) :
          RootSlot (Fin C.card) (MatchingEdge C67.M)) ≤
      ∑ j ∈ (minorBranches P).filter (Aalloc.Fbedge · = e),
        Erdos547b.ZhaoLemma58GroupedSmallForest.orientedClassSize
          (branchForest P).branches orient j c := by
  exact coordinatePoolLoad_edgeb_le hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (factsAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0
    Aalloc
    (moutOriginalEdge
      (R := regularityReducedGraph G cluster epsilon density) D)
    (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
    orient hparity (factsEdgeb_injective G cluster epsilon density D)
    (factsAssignedEdge0_ne_edgeb G cluster epsilon density D C hT P optional
      S clusterCap base0 base1 baseb Aalloc)
    (factsEdge1_disjoint_edgeb G cluster epsilon density D C) e c

include H

/-- Construct the exact capacity record consumed by the rich coordinate
application.  Raw-reservoir largeness is derived uniformly from the host
system.  The remaining three inputs are the literal removal estimate, the
pointwise exact coordinate-pool capacity inequality, and the direct-root Hall
budget; none is an embedding or continuation premise. -/
theorem richCoordinateCapacityFacts
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)
    (removalBudget : ℝ)
    (hrootLarge : (epsilon : ℝ) * #(cluster Aroot) ≤ quota)
    (hcompanionLarge : (epsilon : ℝ) * #(cluster Broot) ≤ quota)
    (hclusterLarge : ∀ x,
      (epsilon : ℝ) * #(cluster x) + (2 * quota : ℕ) ≤ #(cluster x))
    (hremoval : ∀ i a,
      coordinateRemovalBudget (AllocationHierarchy hT P optional)
        (epsilon : ℝ)
        (factsRootSlot G cluster epsilon density D C hT P optional S
          clusterCap base0 base1 baseb Aalloc orient)
        (factsWhole G cluster epsilon density Aroot Broot C)
        (fun i a ↦ factsWhole G cluster epsilon density Aroot Broot C
          (factsInteriorSlot G cluster epsilon density D C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient i a)) i a ≤
          removalBudget)
    (hslotCapacity : ∀ slot,
      RelevantSlot (G := G) (cluster := cluster) (epsilon := epsilon)
          (density := density) (D := D) (C := C) slot →
      (factsCapacity G cluster epsilon density D C hT P optional S
          clusterCap base0 base1 baseb Aalloc orient slot + small + 1 : ℝ) +
          removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(factsRaw G cluster epsilon density C H.rootReserve
            H.companionReserve slot))
    (hdirectBudget :
      (#(Finset.univ.filter fun i ↦
          (AllocationHierarchy hT P optional).parent i = Sum.inl 0) : ℝ) *
        ((epsilon : ℝ) *
          #(factsWhole G cluster epsilon density Aroot Broot C
            (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M)))) < quota) :
    CoordinateCapacityFacts (AllocationHierarchy hT P optional)
      (epsilon : ℝ) (density : ℝ) small
      (factsWhole G cluster epsilon density Aroot Broot C
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
          RootSlot (Fin C.card) (MatchingEdge C67.M)))
      (factsRaw G cluster epsilon density C H.rootReserve H.companionReserve
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
          RootSlot (Fin C.card) (MatchingEdge C67.M)))
      (factsRootSlot G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient)
      (factsWhole G cluster epsilon density Aroot Broot C)
      (factsRaw G cluster epsilon density C H.rootReserve H.companionReserve)
      (factsInteriorSlot G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient)
      (factsCapacity G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient)
      removalBudget := by
  refine
    { sourceLarge := ?_
      rootRawLarge := ?_
      interiorRawLarge := ?_
      removal := hremoval
      rootCapacity := ?_
      interiorCapacity := ?_
      badBudget := ?_ }
  · exact richSlotRaw_large G Gdegree cluster epsilon density D Aroot Broot C
      rhoK Pcluster threshold quota H hrootLarge hcompanionLarge hclusterLarge
      (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
        RootSlot (Fin C.card) (MatchingEdge C67.M))
  · intro i
    exact richSlotRaw_large G Gdegree cluster epsilon density D Aroot Broot C
      rhoK Pcluster threshold quota H hrootLarge hcompanionLarge hclusterLarge
      (factsRootSlot G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient i)
  · intro i a
    exact richSlotRaw_large G Gdegree cluster epsilon density D Aroot Broot C
      rhoK Pcluster threshold quota H hrootLarge hcompanionLarge hclusterLarge
      (factsInteriorSlot G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient i a)
  · intro i
    apply hslotCapacity
    exact coordinateRootSlot_relevant G cluster epsilon density D C hT P
      optional S clusterCap base0 base1 baseb orient
      (factsAllowed0 G cluster epsilon density D C) Aalloc i
  · intro i a
    apply hslotCapacity
    exact coordinateInteriorSlot_relevant G cluster epsilon density D C hT P
      optional S clusterCap base0 base1 baseb orient
      (factsAllowed0 G cluster epsilon density D C) Aalloc i a
  · generalize hs : componentReservoirSide P ⟨0, P.numParts_pos⟩ = side
    fin_cases side
    · simpa [factsRaw, slotRaw, hs,
        H.rootReserve_card] using hdirectBudget
    · simpa [factsRaw, slotRaw, hs,
        H.companionReserve_card] using hdirectBudget

/-- Build the coordinate capacity record from the literal source allocation
loads on the slots which the hierarchy actually generates.  In particular,
the selected-edge bound uses `base0 + small`, excluding the selected branch
roots already placed in their `C` clusters.  The five margin hypotheses are
ordinary scalar host inequalities for the five actual slot classes, not an
embedding or continuation premise. -/
theorem richCoordinateCapacityFacts_of_sourceLoads
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)
    (hparity : OptionalBranchRootParity P optional)
    (rootCap : Fin 2 → ℕ) (removalBudget : ℝ)
    (hrootLarge : (epsilon : ℝ) * #(cluster Aroot) ≤ quota)
    (hcompanionLarge : (epsilon : ℝ) * #(cluster Broot) ≤ quota)
    (hclusterLarge : ∀ x,
      (epsilon : ℝ) * #(cluster x) + (2 * quota : ℕ) ≤ #(cluster x))
    (hremoval : ∀ i a,
      coordinateRemovalBudget (AllocationHierarchy hT P optional)
        (epsilon : ℝ)
        (factsRootSlot G cluster epsilon density D C hT P optional S
          clusterCap base0 base1 baseb Aalloc orient)
        (factsWhole G cluster epsilon density Aroot Broot C)
        (fun i a ↦ factsWhole G cluster epsilon density Aroot Broot C
          (factsInteriorSlot G cluster epsilon density D C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient i a)) i a ≤
          removalBudget)
    (hrootLoad : ∀ side,
      #(rootReservoirSegments hT P optional side) ≤ rootCap side)
    (hrootMargin : ∀ side,
      (rootCap side + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(factsRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inl side : RootSlot (Fin C.card) (MatchingEdge C67.M))))
    (hclusterMargin : ∀ C0,
      (clusterCap + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(factsRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inl C0) :
              RootSlot (Fin C.card) (MatchingEdge C67.M))))
    (hF0Margin : ∀ j ∈ S.selected, ∀ c,
      (base0 + small + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(factsRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inr ⟨moutOriginalEdge
              (R := regularityReducedGraph G cluster epsilon density) D
              (Aalloc.F0edge j), c⟩) :
                RootSlot (Fin C.card) (MatchingEdge C67.M))))
    (hF1Margin : ∀
      (e : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C) c,
      (base1 + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(factsRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inr ⟨e.1, c⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M))))
    (hFbMargin : ∀
      (e : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D) c,
      (baseb + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(factsRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inr ⟨e.1, c⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M))))
    (hdirectBudget :
      (#(Finset.univ.filter fun i ↦
          (AllocationHierarchy hT P optional).parent i = Sum.inl 0) : ℝ) *
        ((epsilon : ℝ) *
          #(factsWhole G cluster epsilon density Aroot Broot C
            (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M)))) < quota) :
    CoordinateCapacityFacts (AllocationHierarchy hT P optional)
      (epsilon : ℝ) (density : ℝ) small
      (factsWhole G cluster epsilon density Aroot Broot C
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
          RootSlot (Fin C.card) (MatchingEdge C67.M)))
      (factsRaw G cluster epsilon density C H.rootReserve H.companionReserve
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
          RootSlot (Fin C.card) (MatchingEdge C67.M)))
      (factsRootSlot G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient)
      (factsWhole G cluster epsilon density Aroot Broot C)
      (factsRaw G cluster epsilon density C H.rootReserve H.companionReserve)
      (factsInteriorSlot G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient)
      (factsCapacity G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient)
      removalBudget := by
  refine
    { sourceLarge := ?_
      rootRawLarge := ?_
      interiorRawLarge := ?_
      removal := hremoval
      rootCapacity := ?_
      interiorCapacity := ?_
      badBudget := ?_ }
  · exact richSlotRaw_large G Gdegree cluster epsilon density D Aroot Broot C
      rhoK Pcluster threshold quota H hrootLarge hcompanionLarge hclusterLarge
      (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
        RootSlot (Fin C.card) (MatchingEdge C67.M))
  · intro i
    exact richSlotRaw_large G Gdegree cluster epsilon density D Aroot Broot C
      rhoK Pcluster threshold quota H hrootLarge hcompanionLarge hclusterLarge
      (factsRootSlot G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient i)
  · intro i a
    exact richSlotRaw_large G Gdegree cluster epsilon density D Aroot Broot C
      rhoK Pcluster threshold quota H hrootLarge hcompanionLarge hclusterLarge
      (factsInteriorSlot G cluster epsilon density D C hT P optional S
        clusterCap base0 base1 baseb Aalloc orient i a)
  · intro i
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        have hslot : factsRootSlot G cluster epsilon density D C hT P optional
              S clusterCap base0 base1 baseb Aalloc orient i =
            (Sum.inl (componentReservoirSide P q) :
              RootSlot (Fin C.card) (MatchingEdge C67.M)) := by
          simp [factsRootSlot, coordinateHierarchyRootSlot, hclass]
        rw [hslot]
        apply capacityMargin_mono _ (rootCap (componentReservoirSide P q))
          small removalBudget _
        · exact coordinatePoolLoad_rootReservoir_le hT P optional S
            (fun _ : Fin C.card ↦ clusterCap)
            (factsAllowed0 G cluster epsilon density D C)
            (fun _ : RemainingMinEdge
              (R := regularityReducedGraph G cluster epsilon density) D C ↦
                base1)
            (fun _ : ReservedEdge
              (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
            base0 Aalloc
            (moutOriginalEdge
              (R := regularityReducedGraph G cluster epsilon density) D)
            (fun e : RemainingMinEdge
              (R := regularityReducedGraph G cluster epsilon density) D C ↦
                e.1)
            (fun e : ReservedEdge
              (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
            orient _ _ (hrootLoad (componentReservoirSide P q))
        · exact hrootMargin (componentReservoirSide P q)
    | inr j =>
        by_cases hj0 : j ∈ S.selected
        · have hslot : factsRootSlot G cluster epsilon density D C hT P optional
                S clusterCap base0 base1 baseb Aalloc orient i =
              (Sum.inr (Sum.inl (Aalloc.F0cluster j)) :
                RootSlot (Fin C.card) (MatchingEdge C67.M)) := by
            simp [factsRootSlot, coordinateHierarchyRootSlot,
              coordinateBranchRootSlot, hclass, hj0]
          rw [hslot]
          apply capacityMargin_mono _ clusterCap small removalBudget _
          · exact coordinatePoolLoad_selectedCluster_le hT P optional S
              (fun _ : Fin C.card ↦ clusterCap)
              (factsAllowed0 G cluster epsilon density D C)
              (fun _ : RemainingMinEdge
                (R := regularityReducedGraph G cluster epsilon density) D C ↦
                  base1)
              (fun _ : ReservedEdge
                (R := regularityReducedGraph G cluster epsilon density) D ↦
                  baseb)
              base0 Aalloc
              (moutOriginalEdge
                (R := regularityReducedGraph G cluster epsilon density) D)
              (fun e : RemainingMinEdge
                (R := regularityReducedGraph G cluster epsilon density) D C ↦
                  e.1)
              (fun e : ReservedEdge
                (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
              orient (Aalloc.F0cluster j)
          · exact hclusterMargin (Aalloc.F0cluster j)
        · by_cases hj1 : j ∈ majorResidualBranches P S
          · have hslot : factsRootSlot G cluster epsilon density D C hT P
                  optional S clusterCap base0 base1 baseb Aalloc orient i =
                (Sum.inr (Sum.inr ⟨(Aalloc.F1edge j).1, orient j 0⟩) :
                  RootSlot (Fin C.card) (MatchingEdge C67.M)) := by
              simp [factsRootSlot, coordinateHierarchyRootSlot,
                coordinateBranchRootSlot, hclass, hj0, hj1]
            rw [hslot]
            apply capacityMargin_mono _ base1 small removalBudget _
            · exact coordinatePoolLoad_edge1_le_capacity hT P optional S
                (fun _ : Fin C.card ↦ clusterCap)
                (factsAllowed0 G cluster epsilon density D C)
                (fun _ : RemainingMinEdge
                  (R := regularityReducedGraph G cluster epsilon density) D C ↦
                    base1)
                (fun _ : ReservedEdge
                  (R := regularityReducedGraph G cluster epsilon density) D ↦
                    baseb)
                base0 Aalloc
                (moutOriginalEdge
                  (R := regularityReducedGraph G cluster epsilon density) D)
                (fun e : RemainingMinEdge
                  (R := regularityReducedGraph G cluster epsilon density) D C ↦
                    e.1)
                (fun e : ReservedEdge
                  (R := regularityReducedGraph G cluster epsilon density) D ↦
                    e.1)
                orient hparity (factsEdge1_injective G cluster epsilon density D C)
                (factsEdge0_disjoint_edge1 G cluster epsilon density D C)
                (factsEdge1_disjoint_edgeb G cluster epsilon density D C)
                (Aalloc.F1edge j) (orient j 0)
            · exact hF1Margin (Aalloc.F1edge j) (orient j 0)
          · have hslot : factsRootSlot G cluster epsilon density D C hT P
                  optional S clusterCap base0 base1 baseb Aalloc orient i =
                (Sum.inr (Sum.inr ⟨(Aalloc.Fbedge j).1, orient j 0⟩) :
                  RootSlot (Fin C.card) (MatchingEdge C67.M)) := by
              simp [factsRootSlot, coordinateHierarchyRootSlot,
                coordinateBranchRootSlot, hclass, hj0, hj1]
            rw [hslot]
            apply capacityMargin_mono _ baseb small removalBudget _
            · exact coordinatePoolLoad_edgeb_le_capacity hT P optional S
                (fun _ : Fin C.card ↦ clusterCap)
                (factsAllowed0 G cluster epsilon density D C)
                (fun _ : RemainingMinEdge
                  (R := regularityReducedGraph G cluster epsilon density) D C ↦
                    base1)
                (fun _ : ReservedEdge
                  (R := regularityReducedGraph G cluster epsilon density) D ↦
                    baseb)
                base0 Aalloc
                (moutOriginalEdge
                  (R := regularityReducedGraph G cluster epsilon density) D)
                (fun e : RemainingMinEdge
                  (R := regularityReducedGraph G cluster epsilon density) D C ↦
                    e.1)
                (fun e : ReservedEdge
                  (R := regularityReducedGraph G cluster epsilon density) D ↦
                    e.1)
                orient hparity (factsEdgeb_injective G cluster epsilon density D)
                (factsAssignedEdge0_ne_edgeb G cluster epsilon density D C hT P
                  optional S clusterCap base0 base1 baseb Aalloc)
                (factsEdge1_disjoint_edgeb G cluster epsilon density D C)
                (Aalloc.Fbedge j) (orient j 0)
            · exact hFbMargin (Aalloc.Fbedge j) (orient j 0)
  · intro i a
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        have hslot : factsInteriorSlot G cluster epsilon density D C hT P
              optional S clusterCap base0 base1 baseb Aalloc orient i a =
            (Sum.inl (componentReservoirSide P q) :
              RootSlot (Fin C.card) (MatchingEdge C67.M)) := by
          unfold factsInteriorSlot coordinateHierarchyInteriorSlot
          rw [hclass]
        rw [hslot]
        apply capacityMargin_mono _ (rootCap (componentReservoirSide P q))
          small removalBudget _
        · exact coordinatePoolLoad_rootReservoir_le hT P optional S
            (fun _ : Fin C.card ↦ clusterCap)
            (factsAllowed0 G cluster epsilon density D C)
            (fun _ : RemainingMinEdge
              (R := regularityReducedGraph G cluster epsilon density) D C ↦
                base1)
            (fun _ : ReservedEdge
              (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
            base0 Aalloc
            (moutOriginalEdge
              (R := regularityReducedGraph G cluster epsilon density) D)
            (fun e : RemainingMinEdge
              (R := regularityReducedGraph G cluster epsilon density) D C ↦
                e.1)
            (fun e : ReservedEdge
              (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
            orient _ _ (hrootLoad (componentReservoirSide P q))
        · exact hrootMargin (componentReservoirSide P q)
    | inr j =>
        have hinterior := coordinateHierarchyInteriorSlot_branch hT P optional S
          (fun _ : Fin C.card ↦ clusterCap)
          (factsAllowed0 G cluster epsilon density D C)
          (fun _ : RemainingMinEdge
            (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
          (fun _ : ReservedEdge
            (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
          base0 Aalloc
          (moutOriginalEdge
            (R := regularityReducedGraph G cluster epsilon density) D)
          (fun e : RemainingMinEdge
            (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
          (fun e : ReservedEdge
            (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
          orient i j hclass a
        unfold factsInteriorSlot
        rw [hinterior]
        by_cases hj0 : j ∈ S.selected
        · simp only [dif_pos hj0]
          apply capacityMargin_mono _ (base0 + small) small removalBudget _
          · exact coordinatePoolLoad_edge0_le_deep hT P optional S
              (fun _ : Fin C.card ↦ clusterCap)
              (factsAllowed0 G cluster epsilon density D C)
              (fun _ : RemainingMinEdge
                (R := regularityReducedGraph G cluster epsilon density) D C ↦
                  base1)
              (fun _ : ReservedEdge
                (R := regularityReducedGraph G cluster epsilon density) D ↦
                  baseb)
              base0 Aalloc
              (moutOriginalEdge
                (R := regularityReducedGraph G cluster epsilon density) D)
              (fun e : RemainingMinEdge
                (R := regularityReducedGraph G cluster epsilon density) D C ↦
                  e.1)
              (fun e : ReservedEdge
                (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
              orient (factsEdge0_injective G cluster epsilon density D)
              (factsEdge0_disjoint_edge1 G cluster epsilon density D C)
              (factsAssignedEdge0_ne_edgeb G cluster epsilon density D C hT P
                optional S clusterCap base0 base1 baseb Aalloc)
              (Aalloc.F0edge j) ⟨j, hj0, rfl⟩
              (orient j (segmentEndpointSide hT P optional i j a))
          · simpa only [Nat.cast_add] using
              hF0Margin j hj0
                (orient j (segmentEndpointSide hT P optional i j a))
        · by_cases hj1 : j ∈ majorResidualBranches P S
          · simp only [dif_neg hj0, dif_pos hj1]
            apply capacityMargin_mono _ base1 small removalBudget _
            · exact coordinatePoolLoad_edge1_le_capacity hT P optional S
                (fun _ : Fin C.card ↦ clusterCap)
                (factsAllowed0 G cluster epsilon density D C)
                (fun _ : RemainingMinEdge
                  (R := regularityReducedGraph G cluster epsilon density) D C ↦
                    base1)
                (fun _ : ReservedEdge
                  (R := regularityReducedGraph G cluster epsilon density) D ↦
                    baseb)
                base0 Aalloc
                (moutOriginalEdge
                  (R := regularityReducedGraph G cluster epsilon density) D)
                (fun e : RemainingMinEdge
                  (R := regularityReducedGraph G cluster epsilon density) D C ↦
                    e.1)
                (fun e : ReservedEdge
                  (R := regularityReducedGraph G cluster epsilon density) D ↦
                    e.1)
                orient hparity (factsEdge1_injective G cluster epsilon density D C)
                (factsEdge0_disjoint_edge1 G cluster epsilon density D C)
                (factsEdge1_disjoint_edgeb G cluster epsilon density D C)
                (Aalloc.F1edge j)
                (orient j (segmentEndpointSide hT P optional i j a))
            · exact hF1Margin (Aalloc.F1edge j)
                (orient j (segmentEndpointSide hT P optional i j a))
          · simp only [dif_neg hj0, dif_neg hj1]
            apply capacityMargin_mono _ baseb small removalBudget _
            · exact coordinatePoolLoad_edgeb_le_capacity hT P optional S
                (fun _ : Fin C.card ↦ clusterCap)
                (factsAllowed0 G cluster epsilon density D C)
                (fun _ : RemainingMinEdge
                  (R := regularityReducedGraph G cluster epsilon density) D C ↦
                    base1)
                (fun _ : ReservedEdge
                  (R := regularityReducedGraph G cluster epsilon density) D ↦
                    baseb)
                base0 Aalloc
                (moutOriginalEdge
                  (R := regularityReducedGraph G cluster epsilon density) D)
                (fun e : RemainingMinEdge
                  (R := regularityReducedGraph G cluster epsilon density) D C ↦
                    e.1)
                (fun e : ReservedEdge
                  (R := regularityReducedGraph G cluster epsilon density) D ↦
                    e.1)
                orient hparity (factsEdgeb_injective G cluster epsilon density D)
                (factsAssignedEdge0_ne_edgeb G cluster epsilon density D C hT P
                  optional S clusterCap base0 base1 baseb Aalloc)
                (factsEdge1_disjoint_edgeb G cluster epsilon density D C)
                (Aalloc.Fbedge j)
                (orient j (segmentEndpointSide hT P optional i j a))
            · exact hFbMargin (Aalloc.Fbedge j)
                (orient j (segmentEndpointSide hT P optional i j a))
  · generalize hs : componentReservoirSide P ⟨0, P.numParts_pos⟩ = side
    fin_cases side
    · simpa [factsRaw, slotRaw, hs, H.rootReserve_card] using hdirectBudget
    · simpa [factsRaw, slotRaw, hs, H.companionReserve_card] using
        hdirectBudget

end Capacity

/-! ## Source-facing whole pairs -/

section Pair

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- Every raw endpoint of a residual `M_1` edge belongs to `V_1`. -/
theorem remainingEndpoint_mem_V1
    (e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C)
    (c : Fin 2) :
    matchingEdgeEndpoint e.1.1 c ∈
      MatchingDecomposition.V1
        (R := regularityReducedGraph G cluster epsilon density) D := by
  apply MatchingDecomposition.Mone_support_subset_V1
    (R := regularityReducedGraph G cluster epsilon density) D C
  exact matchingEndpoint_mem_edgeFinsetSupport (G := G)
    (cluster := cluster) (epsilon := epsilon) (density := density)
    (C67 := C67) (L := L)
    (S := MatchingDecomposition.MoneEdges
      (R := regularityReducedGraph G cluster epsilon density) D C)
    (e := e.1) e.2 c

/-- The genuine Lemma-6.11 `A` row turns every residual endpoint into the
whole regular pair used for a major-residual branch root. -/
theorem remainingEndpointPair_of_V1_adj
    (hV1Adj : ∀ x ∈ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Aroot x)
    (e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C)
    (c : Fin 2) :
    G.IsUniform epsilon (cluster Aroot)
        (cluster (matchingEdgeEndpoint e.1.1 c)) ∧
      density ≤ G.edgeDensity (cluster Aroot)
        (cluster (matchingEdgeEndpoint e.1.1 c)) := by
  exact pair_of_reducedAdj G cluster epsilon density
    (hV1Adj _ (remainingEndpoint_mem_V1 G cluster epsilon density D C e c))

/-- A supplied canonical `M_b` root side and its genuine reduced adjacency
give the whole `B`-facing pair.  The final rich wrapper instantiates this
adjacency with the positive-density theorem, rather than an arbitrary pair
oracle. -/
theorem reservedRootEndpointPair_of_adj
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hMbAdj : ∀ e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Broot
          (matchingEdgeEndpoint e.1.1 (mbSide e)))
    (e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D) :
    G.IsUniform epsilon (cluster Broot)
        (cluster (matchingEdgeEndpoint e.1.1 (mbSide e))) ∧
      density ≤ G.edgeDensity (cluster Broot)
        (cluster (matchingEdgeEndpoint e.1.1 (mbSide e))) := by
  exact pair_of_reducedAdj G cluster epsilon density (hMbAdj e)

include H

/-- In the canonical orientation, a selected branch's local side one is
exactly the accessible endpoint paired with its allocated `C` cluster. -/
theorem canonicalSelectedAccessPair
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (j : BranchIndex P) (hj : j ∈ S.selected) :
    G.IsUniform epsilon
        (indexedCluster cluster C (Aalloc.F0cluster j))
        (cluster (matchingEdgeEndpoint
          (moutOriginalEdge
            (R := regularityReducedGraph G cluster epsilon density) D
            (Aalloc.F0edge j)).1
          (canonicalCoordinateOrientation G cluster epsilon density D C hT P
            optional S clusterCap base0 base1 baseb Aalloc mbSide j 1))) ∧
      density ≤ G.edgeDensity
        (indexedCluster cluster C (Aalloc.F0cluster j))
        (cluster (matchingEdgeEndpoint
          (moutOriginalEdge
            (R := regularityReducedGraph G cluster epsilon density) D
            (Aalloc.F0edge j)).1
          (canonicalCoordinateOrientation G cluster epsilon density D C hT P
            optional S clusterCap base0 base1 baseb Aalloc mbSide j 1))) := by
  have hpair := selected_accessPair G cluster epsilon density D Aroot Broot C
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D)))
    rhoK Pcluster threshold quota Gdegree H (Aalloc.F0cluster j)
    (Aalloc.F0edge j) (Aalloc.F0_allowed j hj)
  simpa only [canonicalCoordinateOrientation_selected_apply G cluster epsilon
    density D C hT P optional S clusterCap base0 base1 baseb Aalloc mbSide j
    hj 1] using hpair

omit H

/-- The canonical residual orientation roots the branch at endpoint zero,
which is paired with distinguished `A` by the Lemma-6.11 `V_1` row. -/
theorem canonicalResidualRootPair
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hV1Adj : ∀ x ∈ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Aroot x)
    (j : BranchIndex P) (hj : j ∈ majorResidualBranches P S) :
    G.IsUniform epsilon (cluster Aroot)
        (cluster (matchingEdgeEndpoint (Aalloc.F1edge j).1.1
          (canonicalCoordinateOrientation G cluster epsilon density D C hT P
            optional S clusterCap base0 base1 baseb Aalloc mbSide j 0))) ∧
      density ≤ G.edgeDensity (cluster Aroot)
        (cluster (matchingEdgeEndpoint (Aalloc.F1edge j).1.1
          (canonicalCoordinateOrientation G cluster epsilon density D C hT P
            optional S clusterCap base0 base1 baseb Aalloc mbSide j 0))) := by
  simpa only [canonicalCoordinateOrientation_residual_apply G cluster epsilon
    density D C hT P optional S clusterCap base0 base1 baseb Aalloc mbSide j
    hj 0] using
      (remainingEndpointPair_of_V1_adj G cluster epsilon density D Aroot C
        hV1Adj (Aalloc.F1edge j) 0)

/-- The canonical minor orientation roots the branch at its prescribed
positive-`B` endpoint. -/
theorem canonicalMinorRootPair
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hMbAdj : ∀ e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Broot
          (matchingEdgeEndpoint e.1.1 (mbSide e)))
    (j : BranchIndex P) (hj : j ∈ minorBranches P) :
    G.IsUniform epsilon (cluster Broot)
        (cluster (matchingEdgeEndpoint (Aalloc.Fbedge j).1.1
          (canonicalCoordinateOrientation G cluster epsilon density D C hT P
            optional S clusterCap base0 base1 baseb Aalloc mbSide j 0))) ∧
      density ≤ G.edgeDensity (cluster Broot)
        (cluster (matchingEdgeEndpoint (Aalloc.Fbedge j).1.1
          (canonicalCoordinateOrientation G cluster epsilon density D C hT P
            optional S clusterCap base0 base1 baseb Aalloc mbSide j 0))) := by
  simpa only [canonicalCoordinateOrientation_minor_zero G cluster epsilon
    density D C hT P optional S clusterCap base0 base1 baseb Aalloc mbSide j
    hj] using
      (reservedRootEndpointPair_of_adj G cluster epsilon density D Broot mbSide
        hMbAdj (Aalloc.Fbedge j))

include H

/-- The two distinguished reservoir sides, in either genuine orientation,
form the stored `A`--`B` whole regular pair. -/
private theorem distinguishedReservoirPair_of_ne
    (sourceSide targetSide : Fin 2) (hne : sourceSide ≠ targetSide) :
    G.IsUniform epsilon
        (factsWhole G cluster epsilon density Aroot Broot C
          (Sum.inl sourceSide : RootSlot (Fin C.card) (MatchingEdge C67.M)))
        (factsWhole G cluster epsilon density Aroot Broot C
          (Sum.inl targetSide : RootSlot (Fin C.card) (MatchingEdge C67.M))) ∧
      density ≤ G.edgeDensity
        (factsWhole G cluster epsilon density Aroot Broot C
          (Sum.inl sourceSide : RootSlot (Fin C.card) (MatchingEdge C67.M)))
        (factsWhole G cluster epsilon density Aroot Broot C
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
  · simpa [factsWhole, slotWhole] using hpair
  · exact ⟨hpair.1.symm, by
      simpa [factsWhole, slotWhole, G.edgeDensity_comm] using hpair.2⟩
  · exact False.elim (hne rfl)

/-- Every hierarchy segment attached directly to the global source root sees
one of the literal rich whole regular pairs.  Component-root children use the
opposite distinguished reserve.  Branch-root children use, respectively,
the selected `A`--`C`, residual `A`--`M₁`, or minor `B`--`M_b` pair in the
canonical coordinate orientation. -/
theorem canonicalDirectPair
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (factsAllowed0 G cluster epsilon density D C)
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
    (i : SegmentIndex hT P optional)
    (hparent : (AllocationHierarchy hT P optional).parent i = Sum.inl 0) :
    let orient := canonicalCoordinateOrientation G cluster epsilon density D C
      hT P optional S clusterCap base0 base1 baseb Aalloc mbSide
    G.IsUniform epsilon
        (factsWhole G cluster epsilon density Aroot Broot C
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
            RootSlot (Fin C.card) (MatchingEdge C67.M)))
        (factsWhole G cluster epsilon density Aroot Broot C
          (factsRootSlot G cluster epsilon density D C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient i)) ∧
      density ≤ G.edgeDensity
        (factsWhole G cluster epsilon density Aroot Broot C
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
            RootSlot (Fin C.card) (MatchingEdge C67.M)))
        (factsWhole G cluster epsilon density Aroot Broot C
          (factsRootSlot G cluster epsilon density D C hT P optional S
            clusterCap base0 base1 baseb Aalloc orient i)) := by
  dsimp only
  rcases directSegment_sourceClass hT P optional i hparent with
      ⟨q, hclass, -⟩ | ⟨j, hclass, howner, -⟩
  · have hne := (directComponentReservoirSide_ne hT P optional i q hparent
      hclass).symm
    have hpair := distinguishedReservoirPair_of_ne G Gdegree cluster epsilon
      density D Aroot Broot C rhoK Pcluster threshold quota H
      (componentReservoirSide P ⟨0, P.numParts_pos⟩)
      (componentReservoirSide P q) hne
    simpa [factsRootSlot, coordinateHierarchyRootSlot, hclass] using hpair
  · rcases branchClass_mem_selected_or_residual_or_minor P S j with
        hj | hj | hj
    · have hsource :
          componentReservoirSide P ⟨0, P.numParts_pos⟩ = 0 := by
        rw [← howner]
        exact componentReservoirSide_owner_eq_zero_of_mem_selected P S j hj
      have hpair := root_selectedPair G cluster epsilon density D Aroot Broot C
        (MatchingDecomposition.V2
            (R := regularityReducedGraph G cluster epsilon density) D ∩
          (matchingSupport (MatchingDecomposition.Mout
              (R := regularityReducedGraph G cluster epsilon density) D) \
            matchingSupport (MatchingDecomposition.Mb
              (R := regularityReducedGraph G cluster epsilon density) D)))
        rhoK Pcluster threshold quota Gdegree H (Aalloc.F0cluster j)
      simpa [factsWhole, slotWhole, factsRootSlot, coordinateHierarchyRootSlot,
        coordinateBranchRootSlot, hclass, hj, hsource] using hpair
    · have hsource :
          componentReservoirSide P ⟨0, P.numParts_pos⟩ = 0 := by
        rw [← howner]
        exact componentReservoirSide_owner_eq_zero_of_mem_majorResidual P S j
          hj
      have hj0 : j ∉ S.selected := (mem_majorResidualBranches P S j).mp hj |>.2
      have hpair := canonicalResidualRootPair G cluster epsilon density D Aroot
        C hT P optional S clusterCap base0 base1 baseb Aalloc mbSide hV1Adj j hj
      simpa [factsWhole, slotWhole, factsRootSlot, coordinateHierarchyRootSlot,
        coordinateBranchRootSlot, hclass, hj0, hj, hsource] using hpair
    · have hsource :
          componentReservoirSide P ⟨0, P.numParts_pos⟩ = 1 := by
        rw [← howner]
        exact componentReservoirSide_owner_eq_one_of_mem_minorBranches P j hj
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
      simpa [factsWhole, slotWhole, factsRootSlot, coordinateHierarchyRootSlot,
        coordinateBranchRootSlot, hclass, hj0, hj1, hsource] using hpair

end Pair

end Erdos547b.ZhaoClaim616RichCoordinateFacts

#print axioms Erdos547b.ZhaoClaim616RichCoordinateFacts.coordinateSeparationFacts_of_indexedHostSystem
#print axioms Erdos547b.ZhaoClaim616RichCoordinateFacts.richSlotRaw_large
#print axioms Erdos547b.ZhaoClaim616RichCoordinateFacts.richCoordinateCapacityFacts
#print axioms Erdos547b.ZhaoClaim616RichCoordinateFacts.richCoordinateCapacityFacts_of_sourceLoads
#print axioms Erdos547b.ZhaoClaim616RichCoordinateFacts.richCoordinatePoolLoad_edge0_le
#print axioms Erdos547b.ZhaoClaim616RichCoordinateFacts.canonicalSelectedAccessPair
#print axioms Erdos547b.ZhaoClaim616RichCoordinateFacts.canonicalResidualRootPair
#print axioms Erdos547b.ZhaoClaim616RichCoordinateFacts.canonicalMinorRootPair
#print axioms Erdos547b.ZhaoClaim616RichCoordinateFacts.canonicalDirectPair
