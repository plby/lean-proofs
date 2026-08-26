/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinatePairFacts
import ErdosProblems.Erdos547b.Claim616CoordinateCanonicalOptional

/-!
# Concrete rich coordinate containment for Claim 6.16

This module fixes the hierarchy marks to the recorded Zhao cut parents and
assembles the checked pair, capacity, and separation fact constructors.  Its
public endpoint takes source allocation and scalar host inequalities only;
there is no copy, embedding, continuation, or `UniformCutForestData` premise.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateContainment

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
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
open Erdos547b.ZhaoClaim616CoordinateOrientation
open Erdos547b.ZhaoClaim616CoordinateCutParents
open Erdos547b.ZhaoClaim616CoordinateCanonicalOptional
open Erdos547b.ZhaoClaim616CoordinateRootLoad
open Erdos547b.ZhaoClaim616RichCoordinateAllocation
open Erdos547b.ZhaoClaim616RichCoordinateApplication
open Erdos547b.ZhaoClaim616RichCoordinateFacts
open Erdos547b.ZhaoClaim616RichCoordinatePairFacts
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest

universe u v w

variable {V : Type u} {B : Type v} {K : Type w}
variable [Fintype V] [DecidableEq V]
variable [Fintype B] [DecidableEq B] [Fintype K] [DecidableEq K]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}
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

abbrev containmentAllowed0 (i : Fin C.card) :=
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

abbrev containmentWhole :=
  slotWhole (G := G) (cluster := cluster) (epsilon := epsilon)
    (density := density) (A := Aroot) (Broot := Broot) (C := C)
    (C67 := C67)

abbrev containmentRaw (rootReserve companionReserve : Finset B) :=
  slotRaw (G := G) (cluster := cluster) (epsilon := epsilon)
    (density := density) (C := C) (C67 := C67)
    rootReserve companionReserve

abbrev containmentRootSlot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P (canonicalOptional P) S
      (fun _ : Fin C.card ↦ clusterCap)
      (containmentAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  coordinateHierarchyRootSlot hT P (canonicalOptional P) S
    (fun _ : Fin C.card ↦ clusterCap)
    (containmentAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0
    Aalloc
    (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) orient

abbrev containmentInteriorSlot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P (canonicalOptional P) S
      (fun _ : Fin C.card ↦ clusterCap)
      (containmentAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
    (fun _ : Fin C.card ↦ clusterCap)
    (containmentAllowed0 G cluster epsilon density D C)
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

/-- Concrete rich Claim-6.16 containment through the cut-aware coordinate
hierarchy. -/
theorem isContained_of_richCoordinateSourceAllocation
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P (canonicalOptional P) S
      (fun _ : Fin C.card ↦ clusterCap)
      (containmentAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hCV1 : C ⊆ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D)
    (hV1Adj : ∀ x ∈ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Aroot x)
    (hMbAdj : ∀ e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Broot
          (matchingEdgeEndpoint e.1.1 (mbSide e)))
    (rootCap : Fin 2 → ℕ) (removalBudget : ℝ)
    (hrootLarge : (epsilon : ℝ) * #(cluster Aroot) ≤ quota)
    (hcompanionLarge : (epsilon : ℝ) * #(cluster Broot) ≤ quota)
    (hclusterLarge : ∀ x,
      (epsilon : ℝ) * #(cluster x) + (2 * quota : ℕ) ≤ #(cluster x))
    (hremoval : ∀ i a,
      coordinateRemovalBudget (AllocationHierarchy hT P (canonicalOptional P))
        (epsilon : ℝ)
        (containmentRootSlot G cluster epsilon density D C hT P S
          clusterCap base0 base1 baseb Aalloc
          (canonicalCoordinateOrientation G cluster epsilon density D C hT P
            (canonicalOptional P) S clusterCap base0 base1 baseb Aalloc mbSide))
        (containmentWhole G cluster epsilon density Aroot Broot C)
        (fun i a ↦ containmentWhole G cluster epsilon density Aroot Broot C
          (containmentInteriorSlot G cluster epsilon density D C hT P S
            clusterCap base0 base1 baseb Aalloc
            (canonicalCoordinateOrientation G cluster epsilon density D C hT P
              (canonicalOptional P) S clusterCap base0 base1 baseb Aalloc
              mbSide) i a)) i a ≤ removalBudget)
    (hrootLoad : ∀ side,
      #(rootReservoirSegments hT P (canonicalOptional P) side) ≤ rootCap side)
    (hrootMargin : ∀ side,
      (rootCap side + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(containmentRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inl side : RootSlot (Fin C.card) (MatchingEdge C67.M))))
    (hclusterMargin : ∀ C0,
      (clusterCap + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(containmentRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inl C0) :
              RootSlot (Fin C.card) (MatchingEdge C67.M))))
    (hF0Margin : ∀ j ∈ S.selected, ∀ c,
      (base0 + small + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(containmentRaw G cluster epsilon density C H.rootReserve
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
          #(containmentRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inr ⟨e.1, c⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M))))
    (hFbMargin : ∀
      (e : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D) c,
      (baseb + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(containmentRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inr ⟨e.1, c⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M))))
    (hdirectBudget :
      (#(Finset.univ.filter fun i ↦
          (AllocationHierarchy hT P (canonicalOptional P)).parent i =
            Sum.inl 0) : ℝ) *
        ((epsilon : ℝ) *
          #(containmentWhole G cluster epsilon density Aroot Broot C
            (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M)))) < quota) :
    T.IsContained G := by
  let optional := canonicalOptional P
  let orient := canonicalCoordinateOrientation G cluster epsilon density D C
    hT P optional S clusterCap base0 base1 baseb Aalloc mbSide
  have hparity : OptionalBranchRootParity P optional :=
    canonicalOptional_parity hT P
  have hcut : cutParentVertices P ⊆ optional :=
    canonicalOptional_covers_cutParents P
  have hsegmentSmall : ∀ i : SegmentIndex hT P optional,
      (AllocationHierarchy hT P optional).segments.size i ≤ small :=
    canonicalOptional_segment_size_le_small hT P hsmall S
  have pairFacts := canonicalCoordinatePairFacts G Gdegree cluster epsilon
    density D Aroot Broot C rhoK Pcluster threshold quota H hT P optional
    hparity hcut S clusterCap base0 base1 baseb Aalloc mbSide hV1Adj hMbAdj
  have capacityFacts := richCoordinateCapacityFacts_of_sourceLoads G Gdegree
    cluster epsilon density D Aroot Broot C rhoK Pcluster threshold quota H hT
    P optional S clusterCap base0 base1 baseb Aalloc orient hparity rootCap
    removalBudget hrootLarge hcompanionLarge hclusterLarge hremoval hrootLoad
    hrootMargin hclusterMargin hF0Margin hF1Margin hFbMargin hdirectBudget
  have separationFacts := coordinateSeparationFacts_of_indexedHostSystem
    G Gdegree cluster epsilon density D Aroot Broot C rhoK Pcluster threshold
    quota H hCV1
  exact isContained_of_richCoordinateHostFacts G Gdegree cluster epsilon density
    D Aroot Broot C rhoK Pcluster threshold quota H hT P optional S clusterCap
    base0 base1 baseb Aalloc orient hsegmentSmall removalBudget pairFacts
    capacityFacts separationFacts

end Erdos547b.ZhaoClaim616RichCoordinateContainment

#print axioms Erdos547b.ZhaoClaim616RichCoordinateContainment.isContained_of_richCoordinateSourceAllocation
