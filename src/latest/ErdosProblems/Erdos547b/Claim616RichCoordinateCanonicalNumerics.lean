/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateContainment
import ErdosProblems.Erdos547b.Claim616RichCoordinateCapacityNumerics
import ErdosProblems.Erdos547b.Claim616CoordinateRootCount

/-!
# Canonical numeric specialization of rich coordinate containment

The distinguished root capacity is fixed to the number of Zhao components.
All literal raw-slot capacity margins are derived from one exact-quota margin
and four common reserve-deleted cluster margins.  Removal and direct-root Hall
remain explicit scalar inputs at this layer.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateCanonicalNumerics

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
open Erdos547b.ZhaoClaim616CoordinateCanonicalOptional
open Erdos547b.ZhaoClaim616CoordinateRootCount
open Erdos547b.ZhaoClaim616CoordinateRootLoad
open Erdos547b.ZhaoClaim616RichCoordinateAllocation
open Erdos547b.ZhaoClaim616RichCoordinateContainment
open Erdos547b.ZhaoClaim616RichCoordinateCapacityNumerics
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59Hierarchical

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

/-- Common host-cluster size and raw-reservoir largeness facts. -/
structure CanonicalClusterScaleFacts
    {Host Index : Type*} [Fintype Host] [DecidableEq Host]
    (cluster : Index → Finset Host) (Aroot Broot : Index)
    (epsilon : ℝ) (quota m : ℕ) : Prop where
  clusterCard : ∀ x, #(cluster x) = m
  rootLarge : epsilon * #(cluster Aroot) ≤ quota
  companionLarge : epsilon * #(cluster Broot) ≤ quota
  ordinaryLarge : ∀ x,
    epsilon * #(cluster x) + (2 * quota : ℕ) ≤ #(cluster x)

/-- The five scalar inequalities from which all literal slot margins are
derived. -/
structure CanonicalMarginScalars
    (parts small clusterCap base0 base1 baseb quota m : ℕ)
    (rho density removalBudget : ℝ) : Prop where
  gap : 0 ≤ density - rho
  root : (parts + small + 1 : ℝ) + removalBudget + 1 ≤
    (density - rho) * quota
  cluster : (clusterCap + small + 1 : ℝ) + removalBudget + 1 ≤
    (density - rho) * (m - 2 * quota : ℕ)
  selected : (base0 + small + small + 1 : ℝ) + removalBudget + 1 ≤
    (density - rho) * (m - 2 * quota : ℕ)
  residual : (base1 + small + 1 : ℝ) + removalBudget + 1 ≤
    (density - rho) * (m - 2 * quota : ℕ)
  minor : (baseb + small + 1 : ℝ) + removalBudget + 1 ≤
    (density - rho) * (m - 2 * quota : ℕ)

/-- Coordinate-removal bounds, packaged independently of the large final
theorem declaration. -/
structure CoordinateRemovalBounds
    {s : ℕ} (F : HierarchicalSegmentForest 1 s)
    {Host RootGroup : Type*} [Fintype Host] [DecidableEq Host]
    (rho : ℝ) (rootGroup : Fin s → RootGroup)
    (rootWhole : RootGroup → Finset Host)
    (interiorWhole : ∀ i, Fin (F.segments.size i) → Finset Host)
    (removalBudget : ℝ) : Prop where
  bound : ∀ i a,
    coordinateRemovalBudget F rho rootGroup rootWhole interiorWhole i a ≤
      removalBudget

/-- Direct-root Hall inequality in a compact, source-generic record. -/
structure DirectHallBound
    {s : ℕ} (F : HierarchicalSegmentForest 1 s)
    {Host : Type*} [Fintype Host] [DecidableEq Host]
    (rho : ℝ) (sourceWhole : Finset Host) (quota : ℕ) : Prop where
  bound :
    (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
      (rho * #sourceWhole) < quota

include H

/-- Canonical numeric wrapper for the concrete coordinate containment
endpoint. -/
theorem isContained_of_richCoordinateCanonicalNumerics
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
    (m : ℕ) (removalBudget : ℝ)
    (scale : CanonicalClusterScaleFacts cluster Aroot Broot
      (epsilon : ℝ) quota m)
    (margins : CanonicalMarginScalars P.numParts small clusterCap base0 base1
      baseb quota m (epsilon : ℝ) (density : ℝ) removalBudget)
    (removal : CoordinateRemovalBounds
      (AllocationHierarchy hT P (canonicalOptional P)) (epsilon : ℝ)
      (containmentRootSlot G cluster epsilon density D C hT P S
        clusterCap base0 base1 baseb Aalloc
        (canonicalCoordinateOrientation G cluster epsilon density D C hT P
          (canonicalOptional P) S clusterCap base0 base1 baseb Aalloc mbSide))
      (containmentWhole G cluster epsilon density Aroot Broot C)
      (fun i a ↦ containmentWhole G cluster epsilon density Aroot Broot C
        (containmentInteriorSlot G cluster epsilon density D C hT P S
          clusterCap base0 base1 baseb Aalloc
          (canonicalCoordinateOrientation G cluster epsilon density D C hT P
            (canonicalOptional P) S clusterCap base0 base1 baseb Aalloc mbSide)
          i a)) removalBudget)
    (directHall : DirectHallBound
      (AllocationHierarchy hT P (canonicalOptional P)) (epsilon : ℝ)
      (containmentWhole G cluster epsilon density Aroot Broot C
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
          RootSlot (Fin C.card) (MatchingEdge C67.M))) quota) :
    T.IsContained G := by
  have hrootLoad : ∀ side,
      #(rootReservoirSegments hT P (canonicalOptional P) side) ≤ P.numParts :=
    card_rootReservoirSegments_le_numParts hT P (canonicalOptional P)
  have hrootMargin : ∀ side,
      (P.numParts + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(containmentRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inl side : RootSlot (Fin C.card) (MatchingEdge C67.M))) := by
    intro side
    fin_cases side
    · simpa [containmentRaw, slotRaw] using
        (capacity_margin_exact_quota H.rootReserve quota P.numParts P.numParts
          small (epsilon : ℝ) (density : ℝ) removalBudget
          H.rootReserve_card le_rfl margins.root)
    · simpa [containmentRaw, slotRaw] using
        (capacity_margin_exact_quota H.companionReserve quota P.numParts
          P.numParts small (epsilon : ℝ) (density : ℝ) removalBudget
          H.companionReserve_card le_rfl margins.root)
  have hordinaryMargin (X : Finset B) (capacity : ℕ)
      (hX : #X = m)
      (hmargin :
        (capacity + small + 1 : ℝ) + removalBudget + 1 ≤
          ((density : ℝ) - (epsilon : ℝ)) * (m - 2 * quota : ℕ)) :
      (capacity + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(removeRootReserves H.rootReserve H.companionReserve X) := by
    exact capacity_margin_removeRootReserves H.rootReserve H.companionReserve X
      quota m capacity capacity small (epsilon : ℝ) (density : ℝ)
      removalBudget H.rootReserve_card H.companionReserve_card hX margins.gap le_rfl
      hmargin
  have hclusterMargin : ∀ C0,
      (clusterCap + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(containmentRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inl C0) :
              RootSlot (Fin C.card) (MatchingEdge C67.M))) := by
    intro C0
    simpa [containmentRaw, slotRaw, indexedCluster] using
      hordinaryMargin (indexedCluster cluster C C0) clusterCap
        (by simpa [indexedCluster] using scale.clusterCard (finsetValue C C0))
        margins.cluster
  have hF0Margin : ∀ j ∈ S.selected, ∀ c,
      (base0 + small + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(containmentRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inr ⟨moutOriginalEdge
              (R := regularityReducedGraph G cluster epsilon density) D
              (Aalloc.F0edge j), c⟩) :
                RootSlot (Fin C.card) (MatchingEdge C67.M))) := by
    intro j _ c
    simpa [containmentRaw, slotRaw] using
      hordinaryMargin
        (cluster (matchingEdgeEndpoint
          (moutOriginalEdge
            (R := regularityReducedGraph G cluster epsilon density) D
            (Aalloc.F0edge j)).1 c))
        (base0 + small)
        (scale.clusterCard _)
        (by simpa only [Nat.cast_add] using margins.selected)
  have hF1Margin : ∀
      (e : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C) c,
      (base1 + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(containmentRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inr ⟨e.1, c⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M))) := by
    intro e c
    simpa [containmentRaw, slotRaw] using
      hordinaryMargin (cluster (matchingEdgeEndpoint e.1.1 c)) base1
        (scale.clusterCard _) margins.residual
  have hFbMargin : ∀
      (e : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D) c,
      (baseb + small + 1 : ℝ) + removalBudget + 1 ≤
        ((density : ℝ) - (epsilon : ℝ)) *
          #(containmentRaw G cluster epsilon density C H.rootReserve
            H.companionReserve
            (Sum.inr (Sum.inr ⟨e.1, c⟩) :
              RootSlot (Fin C.card) (MatchingEdge C67.M))) := by
    intro e c
    simpa [containmentRaw, slotRaw] using
      hordinaryMargin (cluster (matchingEdgeEndpoint e.1.1 c)) baseb
        (scale.clusterCard _) margins.minor
  exact isContained_of_richCoordinateSourceAllocation G Gdegree cluster epsilon
    density D Aroot Broot C rhoK Pcluster threshold quota H hT P hsmall S
    clusterCap base0 base1 baseb Aalloc mbSide hCV1 hV1Adj hMbAdj
    (fun _ ↦ P.numParts) removalBudget scale.rootLarge scale.companionLarge
    scale.ordinaryLarge removal.bound hrootLoad hrootMargin hclusterMargin
    hF0Margin hF1Margin hFbMargin directHall.bound

end Erdos547b.ZhaoClaim616RichCoordinateCanonicalNumerics

#print axioms Erdos547b.ZhaoClaim616RichCoordinateCanonicalNumerics.isContained_of_richCoordinateCanonicalNumerics
