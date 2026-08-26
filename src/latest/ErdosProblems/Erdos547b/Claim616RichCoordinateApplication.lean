/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateSlotRelevance
import ErdosProblems.Erdos547b.Claim616CoordinateHostPairs
import ErdosProblems.Erdos547b.Claim616HierarchicalCoordinateEmbedding

/-!
# Rich Claim 6.16 coordinate application

This is the first concrete application layer for the endpoint-sensitive
coordinate backend.  The source allocation and its literal edge maps are
fixed.  Raw-subset obligations are discharged from the current
`IndexedHostSystem`; collision separation is passed through a compact facts
record constructed from that same system.  Callers otherwise supply only
regular-pair and numeric capacity facts.  No copy, continuation, cleaned
system, or embedding is an input.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateApplication

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.TreePartition
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateHostLayout
open Erdos547b.ZhaoClaim616CoordinateEdgeMaps
open Erdos547b.ZhaoClaim616RichCoordinateAllocation
open Erdos547b.ZhaoClaim616CoordinateSlotRelevance
open Erdos547b.ZhaoClaim616HierarchicalCoordinateEmbedding

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

private abbrev richAllowed0 (i : Fin C.card) :=
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

private abbrev richWhole :=
  slotWhole (G := G) (cluster := cluster) (epsilon := epsilon)
    (density := density) (A := Aroot) (Broot := Broot) (C := C)
    (C67 := C67)

private abbrev richRaw
    (rootReserve companionReserve : Finset B)
    (slot : ZhaoClaim616HierarchicalSourceLayout.RootSlot
      (Fin C.card) (MatchingEdge C67.M)) : Finset B :=
  slotRaw (G := G) (cluster := cluster) (epsilon := epsilon)
    (density := density) (C := C) (C67 := C67)
    rootReserve companionReserve slot

private abbrev richRootSlotFn
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (richAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  coordinateHierarchyRootSlot hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (richAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0 Aalloc
    (fun e : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) orient

private abbrev richInteriorSlotFn
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (richAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  coordinateHierarchyInteriorSlot hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (richAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0 Aalloc
    (moutOriginalEdge (R := regularityReducedGraph G cluster epsilon density) D) (fun e : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) orient

private abbrev richCoordinateCapacityFn
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (richAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  exactCoordinateCapacity hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (richAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0 Aalloc
    (moutOriginalEdge (R := regularityReducedGraph G cluster epsilon density) D) (fun e : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) orient

/-- The six regular-pair obligations used by the coordinate hierarchy,
factored from the final theorem header so Lean elaborates them independently. -/
structure CoordinatePairFacts
    {s : ℕ} (F : Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest 1 s)
    {Host : Type*} [Fintype Host] [DecidableEq Host]
    (G : SimpleGraph Host) [DecidableRel G.Adj]
    (rho density : ℝ) (sourceWhole : Finset Host)
    {RootGroup : Type*} (rootGroup : Fin s → RootGroup)
    (rootWhole : RootGroup → Finset Host)
    (interiorWhole : ∀ i, Fin (F.segments.size i) → Finset Host) : Prop where
  directUniform : ∀ i, F.parent i = Sum.inl 0 →
    G.IsUniform rho sourceWhole (rootWhole (rootGroup i))
  directDensity : ∀ i, F.parent i = Sum.inl 0 →
    density ≤ G.edgeDensity sourceWhole (rootWhole (rootGroup i))
  attachUniform : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
    G.IsUniform rho
      (Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
        F rootGroup rootWhole interiorWhole j a)
      (rootWhole (rootGroup i))
  attachDensity : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
    density ≤ G.edgeDensity
      (Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
        F rootGroup rootWhole interiorWhole j a)
      (rootWhole (rootGroup i))
  internalUniform : ∀ i a b, (F.segments.tree i).Adj a b →
    b ≠ F.segments.root i →
    G.IsUniform rho
      (Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
        F rootGroup rootWhole interiorWhole i a)
      (interiorWhole i b)
  internalDensity : ∀ i a b, (F.segments.tree i).Adj a b →
    b ≠ F.segments.root i →
    density ≤ G.edgeDensity
      (Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
        F rootGroup rootWhole interiorWhole i a)
      (interiorWhole i b)

/-- Reservoir-size, removal, load-capacity, and direct-root Hall inequalities,
separately packaged from the regular-pair facts. -/
structure CoordinateCapacityFacts
    {s : ℕ} (F : Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest 1 s)
    {Host : Type*} [Fintype Host] [DecidableEq Host]
    (rho density : ℝ) (small : ℕ)
    (sourceWhole sourceRaw : Finset Host)
    {RootGroup : Type*} [DecidableEq RootGroup]
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset Host)
    (interiorGroup : ∀ i, Fin (F.segments.size i) → RootGroup)
    (poolCapacity : RootGroup → ℕ) (removalBudget : ℝ) : Prop where
  sourceLarge : rho * #sourceWhole ≤ #sourceRaw
  rootRawLarge : ∀ i,
    rho * #(rootWhole (rootGroup i)) ≤ #(rootRaw (rootGroup i))
  interiorRawLarge : ∀ i a,
    rho * #(rootWhole (interiorGroup i a)) ≤
      #(rootRaw (interiorGroup i a))
  removal : ∀ i a,
    Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest.coordinateRemovalBudget
      F rho rootGroup rootWhole (fun i a ↦ rootWhole (interiorGroup i a)) i a ≤
        removalBudget
  rootCapacity : ∀ i,
    (poolCapacity (rootGroup i) + small + 1 : ℝ) + removalBudget + 1 ≤
      (density - rho) * #(rootRaw (rootGroup i))
  interiorCapacity : ∀ i a,
    (poolCapacity (interiorGroup i a) + small + 1 : ℝ) +
        removalBudget + 1 ≤
      (density - rho) * #(rootRaw (interiorGroup i a))
  badBudget :
    (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
      (rho * #sourceWhole) < #sourceRaw

/-- Pairwise separation of the raw reservoirs used by relevant coordinate
slots.  Keeping this independent of the concrete host-system parameters makes
the final containment declaration cheap to elaborate. -/
structure CoordinateSeparationFacts
    {Slot Host : Type*} [DecidableEq Host]
    (raw : Slot → Finset Host) (relevant : Slot → Prop) : Prop where
  disjoint : ∀ x y, relevant x → relevant y → x ≠ y →
    Disjoint (raw x) (raw y)

private abbrev RichCoordinatePairFacts
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (richAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2) :=
  CoordinatePairFacts (AllocationHierarchy hT P optional) G
    (epsilon : ℝ) (density : ℝ)
    (richWhole (G := G) (cluster := cluster) (epsilon := epsilon)
      (density := density) (Aroot := Aroot) (Broot := Broot) (C := C)
      (C67 := C67)
      (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))
    (richRootSlotFn G cluster epsilon density D C hT P optional S
      clusterCap base0 base1 baseb Aalloc orient)
    (richWhole (G := G) (cluster := cluster) (epsilon := epsilon)
      (density := density) (Aroot := Aroot) (Broot := Broot) (C := C)
      (C67 := C67))
    (fun i a ↦
      richWhole (G := G) (cluster := cluster) (epsilon := epsilon)
        (density := density) (Aroot := Aroot) (Broot := Broot) (C := C)
        (C67 := C67)
        (richInteriorSlotFn G cluster epsilon density D C hT P optional S
          clusterCap base0 base1 baseb Aalloc orient i a))

private abbrev RichCoordinateCapacityFacts
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (richAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)
    (rootReserve companionReserve : Finset B) (removalBudget : ℝ) :=
  CoordinateCapacityFacts (AllocationHierarchy hT P optional)
    (epsilon : ℝ) (density : ℝ) small
    (richWhole (G := G) (cluster := cluster) (epsilon := epsilon)
      (density := density) (Aroot := Aroot) (Broot := Broot) (C := C)
      (C67 := C67)
      (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))
    (richRaw (G := G) (cluster := cluster) (epsilon := epsilon)
      (density := density) (C := C) (C67 := C67)
      rootReserve companionReserve
      (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
        ZhaoClaim616HierarchicalSourceLayout.RootSlot
          (Fin C.card) (MatchingEdge C67.M)))
    (richRootSlotFn G cluster epsilon density D C hT P optional S
      clusterCap base0 base1 baseb Aalloc orient)
    (richWhole (G := G) (cluster := cluster) (epsilon := epsilon)
      (density := density) (Aroot := Aroot) (Broot := Broot) (C := C)
      (C67 := C67))
    (richRaw (G := G) (cluster := cluster) (epsilon := epsilon)
      (density := density) (C := C) (C67 := C67)
      rootReserve companionReserve)
    (richInteriorSlotFn G cluster epsilon density D C hT P optional S
      clusterCap base0 base1 baseb Aalloc orient)
    (richCoordinateCapacityFn G cluster epsilon density D C hT P optional S
      clusterCap base0 base1 baseb Aalloc orient)
    removalBudget

private abbrev RichCoordinateSeparationFacts
    (rootReserve companionReserve : Finset B) :=
  CoordinateSeparationFacts
    (richRaw (G := G) (cluster := cluster) (epsilon := epsilon)
      (density := density) (C := C) (C67 := C67)
      rootReserve companionReserve)
    (RelevantSlot (G := G) (cluster := cluster) (epsilon := epsilon)
      (density := density) (D := D) (C := C))

/-- Literal containment from one genuine rich source allocation.  Raw
reservoir subsets are proved here from `H`; disjointness, regularity, and
cardinality/capacity inputs are packaged as proof-data records, never as an
embedding result. -/
theorem isContained_of_richCoordinateHostFacts
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (richAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)
    (hsegmentSmall : ∀ i,
      (AllocationHierarchy hT P optional).segments.size i ≤ small)
    (removalBudget : ℝ)
    (pairFacts : RichCoordinatePairFacts G cluster epsilon density D Aroot Broot C
      hT P optional S clusterCap base0 base1 baseb Aalloc orient)
    (capacityFacts : RichCoordinateCapacityFacts G cluster epsilon density D
      Aroot Broot C hT P optional S clusterCap base0 base1 baseb Aalloc orient
      H.rootReserve H.companionReserve removalBudget)
    (separationFacts : RichCoordinateSeparationFacts G cluster epsilon density
      D C H.rootReserve H.companionReserve) :
    T.IsContained G := by
  let rootSlot : SegmentIndex hT P optional →
      ZhaoClaim616HierarchicalSourceLayout.RootSlot
        (Fin C.card) (MatchingEdge C67.M) :=
    richRootSlotFn G cluster epsilon density D C hT P optional S clusterCap base0 base1 baseb Aalloc orient
  let interiorSlot : ∀ i : SegmentIndex hT P optional,
      Fin ((AllocationHierarchy hT P optional).segments.size i) →
        ZhaoClaim616HierarchicalSourceLayout.RootSlot
          (Fin C.card) (MatchingEdge C67.M) :=
    richInteriorSlotFn G cluster epsilon density D C hT P optional S clusterCap base0 base1 baseb Aalloc orient
  have hrootRelevant : ∀ i, RelevantSlot (G := G) (cluster := cluster)
      (epsilon := epsilon) (density := density) (D := D) (C := C)
      (rootSlot i) := by
    intro i
    exact coordinateRootSlot_relevant G cluster epsilon density D C hT P
      optional S clusterCap base0 base1 baseb orient
      (richAllowed0 G cluster epsilon density D C) Aalloc i
  have hinteriorRelevant : ∀ i a,
      RelevantSlot (G := G) (cluster := cluster) (epsilon := epsilon)
        (density := density) (D := D) (C := C) (interiorSlot i a) := by
    intro i a
    exact coordinateInteriorSlot_relevant G cluster epsilon density D C hT P
      optional S clusterCap base0 base1 baseb orient
      (richAllowed0 G cluster epsilon density D C) Aalloc i a
  have hrawSubset
      (slot : ZhaoClaim616HierarchicalSourceLayout.RootSlot
        (Fin C.card) (MatchingEdge C67.M)) :
      richRaw (G := G) (cluster := cluster) (epsilon := epsilon)
          (density := density) (C := C) (C67 := C67)
          H.rootReserve H.companionReserve slot ⊆
        richWhole (G := G) (cluster := cluster) (epsilon := epsilon)
          (density := density) (Aroot := Aroot) (Broot := Broot)
          (C := C) (C67 := C67) slot := by
    rcases slot with side | selected_or_edge
    · fin_cases side
      · simpa [richRaw, richWhole, slotRaw, slotWhole] using
          H.rootReserve_subset
      · simpa [richRaw, richWhole, slotRaw, slotWhole] using
          H.companionReserve_subset
    · rcases selected_or_edge with i | edge
      · simpa [richRaw, richWhole, slotRaw, slotWhole] using
          (removeRootReserves_subset H.rootReserve H.companionReserve
            (indexedCluster cluster C i))
      · rcases edge with ⟨e, side⟩
        simpa [richRaw, richWhole, slotRaw, slotWhole] using
          (removeRootReserves_subset H.rootReserve H.companionReserve
            (cluster (matchingEdgeEndpoint e.1 side)))
  apply isContained_of_coordinateHostFacts hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (richAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0 Aalloc
    (moutOriginalEdge (R := regularityReducedGraph G cluster epsilon density) D) (fun e : RemainingMinEdge (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) orient G
    (epsilon : ℝ) (density : ℝ)
    (richWhole (G := G) (cluster := cluster) (epsilon := epsilon) (density := density) (Aroot := Aroot) (Broot := Broot) (C := C) (C67 := C67)
      (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))
    (richRaw (G := G) (cluster := cluster) (epsilon := epsilon) (density := density) (C := C) (C67 := C67) H.rootReserve H.companionReserve
      (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
        ZhaoClaim616HierarchicalSourceLayout.RootSlot
          (Fin C.card) (MatchingEdge C67.M)))
    (richWhole (G := G) (cluster := cluster) (epsilon := epsilon) (density := density) (Aroot := Aroot) (Broot := Broot) (C := C) (C67 := C67))
    (richRaw (G := G) (cluster := cluster) (epsilon := epsilon) (density := density) (C := C) (C67 := C67) H.rootReserve H.companionReserve)
    removalBudget hsegmentSmall
  · exact hrawSubset
      (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩) :
        ZhaoClaim616HierarchicalSourceLayout.RootSlot
          (Fin C.card) (MatchingEdge C67.M))
  · exact capacityFacts.sourceLarge
  · intro i
    exact hrawSubset (rootSlot i)
  · intro i a
    exact hrawSubset (interiorSlot i a)
  · exact capacityFacts.rootRawLarge
  · exact capacityFacts.interiorRawLarge
  · exact pairFacts.directUniform
  · exact pairFacts.directDensity
  · exact pairFacts.attachUniform
  · exact pairFacts.attachDensity
  · exact pairFacts.internalUniform
  · exact pairFacts.internalDensity
  · exact capacityFacts.removal
  · exact capacityFacts.rootCapacity
  · exact capacityFacts.interiorCapacity
  · exact capacityFacts.badBudget
  · intro i j hij
    exact separationFacts.disjoint (rootSlot i) (rootSlot j)
      (hrootRelevant i) (hrootRelevant j) hij
  · intro i a j b hij
    exact separationFacts.disjoint (interiorSlot i a) (interiorSlot j b)
      (hinteriorRelevant i a) (hinteriorRelevant j b) hij
  · intro i j a hij
    exact separationFacts.disjoint (rootSlot i) (interiorSlot j a)
      (hrootRelevant i) (hinteriorRelevant j a) hij

end Erdos547b.ZhaoClaim616RichCoordinateApplication

#print axioms Erdos547b.ZhaoClaim616RichCoordinateApplication.isContained_of_richCoordinateHostFacts
