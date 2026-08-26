/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615HierarchicalCoordinateSourceLayout
import ErdosProblems.Erdos547b.HierarchicalCoordinatePools

/-!
# Distinguished-reservoir load for coordinate Claim 6.15

Only a segment root can occupy one of the two distinguished reservoirs.
Component-class segments are singletons, and every branch-class interior
coordinate occupies a matching endpoint.  Consequently each segment
contributes at most one vertex to either distinguished pool.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615CoordinateRootLoad

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

section

variable
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional distinguished : Finset V)
    (distinguishedSide : V → Fin 2)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {K0 K1 Kb Edge : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    [DecidableEq Edge]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)

private abbrev rootSlot :=
  coordinateHierarchyRootSlot hT P optional distinguished distinguishedSide S
    capacity0 capacity1 capacityb A edge0 edge1 edgeb orient

private abbrev interiorSlot :=
  coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
    capacityb A edge0 edge1 edgeb orient

private theorem interiorCoordinatesAt_reserve_eq_empty
    (i : SegmentIndex hT P optional) (side : Fin 2) :
    interiorCoordinatesAtPool (AllocationHierarchy hT P optional)
        (interiorSlot hT P optional S capacity0 capacity1 capacityb A edge0
          edge1 edgeb orient) i (Sum.inl side : RootSlot Edge) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have ha' := Finset.mem_filter.mp ha
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      have hiRoot : i ∈ rootSegments hT P optional :=
        (mem_rootSegments_iff hT P optional i).2 ⟨q, hclass⟩
      have hsize := rootSegment_size_eq_one hT P optional i hiRoot
      exact ha'.2.1 (Fin.ext (by omega))
  | inr j =>
      have heq := ha'.2.2
      change coordinateHierarchyInteriorSlot hT P optional S capacity0
          capacity1 capacityb A edge0 edge1 edgeb orient i a =
        (Sum.inl side : RootSlot Edge) at heq
      rw [coordinateHierarchyInteriorSlot_branch hT P optional S capacity0
        capacity1 capacityb A edge0 edge1 edgeb orient i j hclass a] at heq
      simp [coordinateBranchSlot] at heq

/-- Each hierarchy segment contributes at most its root to a distinguished
reservoir.  Thus either distinguished load is bounded by the number of
segments, independently of the three matching packings. -/
theorem coordinatePoolLoad_reserve_le_card_segments (side : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (rootSlot hT P optional distinguished distinguishedSide S capacity0
          capacity1 capacityb A edge0 edge1 edgeb orient)
        (interiorSlot hT P optional S capacity0 capacity1 capacityb A edge0
          edge1 edgeb orient)
        (Sum.inl side : RootSlot Edge) ≤
      Fintype.card (SegmentIndex hT P optional) := by
  classical
  rw [coordinatePoolLoad]
  calc
    (∑ i, coordinatePoolWeight (AllocationHierarchy hT P optional)
        (rootSlot hT P optional distinguished distinguishedSide S capacity0
          capacity1 capacityb A edge0 edge1 edgeb orient)
        (interiorSlot hT P optional S capacity0 capacity1 capacityb A edge0
          edge1 edgeb orient) i (Sum.inl side : RootSlot Edge)) ≤
        ∑ _i : SegmentIndex hT P optional, 1 := by
      apply Finset.sum_le_sum
      intro i _
      rw [coordinatePoolWeight,
        interiorCoordinatesAt_reserve_eq_empty hT P optional S capacity0
          capacity1 capacityb A edge0 edge1 edgeb orient i side]
      simp only [Finset.card_empty, Nat.add_zero]
      split <;> omega
    _ = Fintype.card (SegmentIndex hT P optional) := by simp

end

end Erdos547b.ZhaoClaim615CoordinateRootLoad

#print axioms Erdos547b.ZhaoClaim615CoordinateRootLoad.coordinatePoolLoad_reserve_le_card_segments
