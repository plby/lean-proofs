/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichCoordinateCapacityFacts
import ErdosProblems.Erdos547b.Claim615RichCoordinateOrientedPairFacts

/-!
# Endpoint-exact capacity facts for coordinate Claim 6.15

Zhao's Lemma 5.8 controls the two endpoints of a matching edge separately.
This module packages those literal endpoint loads directly; it does not
replace them by one (generally false) symmetric bin capacity.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichCoordinateOrientedCapacityFacts

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools
open Erdos547b.ZhaoHierarchicalCoordinateContainment
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest

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

/-- Construct the hierarchy capacity certificate from the exact load of each
physical endpoint used by one source family. -/
theorem richCoordinateCapacityFacts_of_endpointLoads
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional distinguished : Finset V)
    (distinguishedSide : V → Fin 2)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {K0 K1 Kb : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → MatchingEdge Q.claim67.M)
    (edge1 : K1 → MatchingEdge Q.claim67.M)
    (edgeb : Kb → MatchingEdge Q.claim67.M)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (rho density removalBudget : ℝ)
    (hsegmentSmall : ∀ i,
      (AllocationHierarchy hT P optional).segments.size i ≤ small)
    (hrawLarge : ∀ slot : RootSlot (MatchingEdge Q.claim67.M),
      rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q slot) ≤
        #(slotRaw Pcluster Gdegree threshold quota R miss Q slot))
    (hremoval : ∀ i a,
      coordinateRemovalBudget (AllocationHierarchy hT P optional) rho
        (coordinateHierarchyRootSlot hT P optional distinguished
          distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1
          edgeb orient)
        (slotWhole Pcluster Gdegree threshold quota R miss Q)
        (fun i a ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
          (coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
            capacityb A edge0 edge1 edgeb orient i a)) i a ≤ removalBudget)
    (hreserveCapacity : ∀ side,
      (coordinatePoolLoad (AllocationHierarchy hT P optional)
            (coordinateHierarchyRootSlot hT P optional distinguished
              distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1
              edgeb orient)
            (coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
              capacityb A edge0 edge1 edgeb orient)
            (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) *
          #(slotRaw Pcluster Gdegree threshold quota R miss Q (Sum.inl side)))
    (h0Capacity : ∀ e c,
      (coordinatePoolLoad (AllocationHierarchy hT P optional)
            (coordinateHierarchyRootSlot hT P optional distinguished
              distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1
              edgeb orient)
            (coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
              capacityb A edge0 edge1 edgeb orient)
            (Sum.inr ⟨edge0 e, c⟩ : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edge0 e, c⟩)))
    (h1Capacity : ∀ e c,
      (coordinatePoolLoad (AllocationHierarchy hT P optional)
            (coordinateHierarchyRootSlot hT P optional distinguished
              distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1
              edgeb orient)
            (coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
              capacityb A edge0 edge1 edgeb orient)
            (Sum.inr ⟨edge1 e, c⟩ : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edge1 e, c⟩)))
    (hbCapacity : ∀ e c,
      (coordinatePoolLoad (AllocationHierarchy hT P optional)
            (coordinateHierarchyRootSlot hT P optional distinguished
              distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1
              edgeb orient)
            (coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
              capacityb A edge0 edge1 edgeb orient)
            (Sum.inr ⟨edgeb e, c⟩ : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edgeb e, c⟩)))
    (hbadBudget :
      (#(Finset.univ.filter fun i ↦
          (AllocationHierarchy hT P optional).parent i = Sum.inl 0) : ℝ) *
        (rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) <
        #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) :
    CoordinateHierarchyCapacityFacts (small := small)
      (AllocationHierarchy hT P optional) rho density
      (slotWhole Pcluster Gdegree threshold quota R miss Q
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))
      (slotRaw Pcluster Gdegree threshold quota R miss Q
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))
      (coordinateHierarchyRootSlot hT P optional distinguished
        distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1 edgeb
        orient)
      (coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
        capacityb A edge0 edge1 edgeb orient)
      (slotWhole Pcluster Gdegree threshold quota R miss Q)
      (slotRaw Pcluster Gdegree threshold quota R miss Q)
      removalBudget := by
  let F := AllocationHierarchy hT P optional
  let rslot := coordinateHierarchyRootSlot hT P optional distinguished
    distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1 edgeb orient
  let islot := coordinateHierarchyInteriorSlot hT P optional S capacity0
    capacity1 capacityb A edge0 edge1 edgeb orient
  have hrootCapacity (i : SegmentIndex hT P optional) :
      (coordinatePoolLoad F rslot islot (rslot i) + small + 1 : ℝ) +
          removalBudget + 1 ≤
        (density - rho) *
          #(slotRaw Pcluster Gdegree threshold quota R miss Q (rslot i)) := by
    by_cases hi : SegmentRootOriginal hT P optional i ∈ distinguished
    · rw [show rslot i = Sum.inl
          (distinguishedSide (SegmentRootOriginal hT P optional i)) by
        exact coordinateHierarchyRootSlot_distinguished hT P optional
          distinguished distinguishedSide S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb orient i hi]
      exact hreserveCapacity _
    · cases hclass : segmentSourceClass hT P optional i with
      | inl q =>
          rw [show rslot i = Sum.inl (componentReservoirSide P q) by
            exact coordinateHierarchyRootSlot_component hT P optional
              distinguished distinguishedSide S capacity0 capacity1 capacityb A
              edge0 edge1 edgeb orient i q hi hclass]
          exact hreserveCapacity _
      | inr j =>
          rw [show rslot i = coordinateBranchSlot P S capacity0 capacity1
              capacityb A edge0 edge1 edgeb orient j
              (segmentEndpointSide hT P optional i j (F.segments.root i)) by
            exact coordinateHierarchyRootSlot_branch hT P optional distinguished
              distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1
              edgeb orient i j hi hclass]
          unfold coordinateBranchSlot coordinateBranchEdge
          split
          · exact h0Capacity _ _
          · split
            · exact h1Capacity _ _
            · exact hbCapacity _ _
  have hinteriorCapacity (i : SegmentIndex hT P optional)
      (a : Fin (F.segments.size i)) :
      (coordinatePoolLoad F rslot islot (islot i a) + small + 1 : ℝ) +
          removalBudget + 1 ≤
        (density - rho) *
          #(slotRaw Pcluster Gdegree threshold quota R miss Q (islot i a)) := by
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        rw [show islot i a = Sum.inl (componentReservoirSide P q) by
          exact coordinateHierarchyInteriorSlot_component hT P optional S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i q hclass a]
        exact hreserveCapacity _
    | inr j =>
        rw [show islot i a = coordinateBranchSlot P S capacity0 capacity1
            capacityb A edge0 edge1 edgeb orient j
            (segmentEndpointSide hT P optional i j a) by
          exact coordinateHierarchyInteriorSlot_branch hT P optional S capacity0
            capacity1 capacityb A edge0 edge1 edgeb orient i j hclass a]
        unfold coordinateBranchSlot coordinateBranchEdge
        split
        · exact h0Capacity _ _
        · split
          · exact h1Capacity _ _
          · exact hbCapacity _ _
  refine {
    segment_small := hsegmentSmall
    source_large := hrawLarge
      (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩))
    root_raw_large := fun i ↦ hrawLarge (rslot i)
    interior_raw_large := fun i a ↦ hrawLarge (islot i a)
    removal := hremoval
    root_capacity := hrootCapacity
    interior_capacity := hinteriorCapacity
    bad_budget := hbadBudget
  }

end Erdos547b.ZhaoClaim615RichCoordinateOrientedCapacityFacts

#print axioms Erdos547b.ZhaoClaim615RichCoordinateOrientedCapacityFacts.richCoordinateCapacityFacts_of_endpointLoads
