/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615HierarchicalCoordinateHostPools
import ErdosProblems.Erdos547b.Claim615HierarchicalCoordinateSourceLayout
import ErdosProblems.Erdos547b.HierarchicalCoordinateContainment

/-!
# Rich coordinate application for Zhao Claim 6.15

This module fixes the literal rich `A₀/B₀` and matching-endpoint reservoirs
and discharges every subset and collision obligation of the generic
coordinate backend.  Pair classification and numeric capacity estimates are
kept in separate proof-data records; neither record contains a copy,
continuation, or containment result.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichCoordinateApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
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

private abbrev RichSlot :=
  ZhaoClaim615CoordinateSourceAllocation.RootSlot
    (MatchingEdge Q.claim67.M)

/-- Containment from one literal rich coordinate allocation.  The only
inputs not derived here are ordinary pair and scalar-capacity facts. -/
theorem isContained_of_richCoordinateHostFacts
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
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → MatchingEdge Q.claim67.M)
    (edge1 : K1 → MatchingEdge Q.claim67.M)
    (edgeb : Kb → MatchingEdge Q.claim67.M)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density removalBudget : ℝ)
    (pairFacts : CoordinateHierarchyPairFacts
      (AllocationHierarchy hT P optional) G rho density
      (slotWhole Pcluster Gdegree threshold quota R miss Q
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))
      (coordinateHierarchyRootSlot hT P optional distinguished
        distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1 edgeb
        orient)
      (slotWhole Pcluster Gdegree threshold quota R miss Q)
      (coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
        capacityb A edge0 edge1 edgeb orient))
    (capacityFacts : CoordinateHierarchyCapacityFacts (small := small)
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
      removalBudget) :
    T.IsContained G := by
  let rootSlot : SegmentIndex hT P optional →
      RichSlot Pcluster Gdegree threshold quota R miss Q :=
    coordinateHierarchyRootSlot hT P optional distinguished distinguishedSide S
      capacity0 capacity1 capacityb A edge0 edge1 edgeb orient
  let interiorSlot : (i : SegmentIndex hT P optional) →
      Fin ((AllocationHierarchy hT P optional).segments.size i) →
        RichSlot Pcluster Gdegree threshold quota R miss Q :=
    coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
      capacityb A edge0 edge1 edgeb orient
  let whole := slotWhole Pcluster Gdegree threshold quota R miss Q
  let raw := slotRaw Pcluster Gdegree threshold quota R miss Q
  let sourceSlot : RichSlot Pcluster Gdegree threshold quota R miss Q :=
    Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)
  apply isContained_of_coordinateHierarchyHostFacts hT P optional G rho
    density (whole sourceSlot) (raw sourceSlot) rootSlot interiorSlot whole raw
    removalBudget
  exact {
    segment_small := capacityFacts.segment_small
    source_subset :=
      slotRaw_subset_slotWhole Pcluster Gdegree threshold quota R miss Q
        sourceSlot
    source_large := capacityFacts.source_large
    root_raw_subset := fun i ↦
      slotRaw_subset_slotWhole Pcluster Gdegree threshold quota R miss Q
        (rootSlot i)
    interior_raw_subset := fun i a ↦
      slotRaw_subset_slotWhole Pcluster Gdegree threshold quota R miss Q
        (interiorSlot i a)
    root_raw_large := capacityFacts.root_raw_large
    interior_raw_large := capacityFacts.interior_raw_large
    direct_uniform := pairFacts.direct_uniform
    direct_density := pairFacts.direct_density
    attach_uniform := pairFacts.attach_uniform
    attach_density := pairFacts.attach_density
    internal_uniform := pairFacts.internal_uniform
    internal_density := pairFacts.internal_density
    removal := capacityFacts.removal
    root_capacity := capacityFacts.root_capacity
    interior_capacity := capacityFacts.interior_capacity
    bad_budget := capacityFacts.bad_budget
    root_raw_disjoint := fun i j h ↦
      slotRaw_disjoint_of_ne Pcluster Gdegree threshold quota R miss Q
        (rootSlot i) (rootSlot j) h
    interior_raw_disjoint := fun i a j b h ↦
      slotRaw_disjoint_of_ne Pcluster Gdegree threshold quota R miss Q
        (interiorSlot i a) (interiorSlot j b) h
    root_interior_raw_disjoint := fun i j a h ↦
      slotRaw_disjoint_of_ne Pcluster Gdegree threshold quota R miss Q
        (rootSlot i) (interiorSlot j a) h
  }

end Erdos547b.ZhaoClaim615RichCoordinateApplication

#print axioms Erdos547b.ZhaoClaim615RichCoordinateApplication.isContained_of_richCoordinateHostFacts
