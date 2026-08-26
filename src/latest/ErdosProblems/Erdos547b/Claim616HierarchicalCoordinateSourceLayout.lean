/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchicalSourceLayout
import ErdosProblems.Erdos547b.HierarchicalCoordinatePools

/-!
# Coordinate-sensitive Claim 6.16 source layout

The coarse Claim 6.16 layout deliberately forgets the endpoint of a matching
edge.  That is suitable for collision separation but too coarse for Zhao's
Lemma 5.8 capacity argument.  Here the physical pool is the existing
`RootSlot` itself, so each matching edge has two distinct endpoint pools.
The orientation may vary from canonical branch to canonical branch, as it does
in the threshold-switch and Appendix-A constructions.

Selected `F₀` segment roots stay in their assigned `C` cluster while their
non-root coordinates use the oriented endpoint of the accessible matching
edge.  Residual and minor segment roots use the endpoint occupied by the
canonical branch root (local side zero).  No host or embedding data occurs in
these definitions.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

section Allocated

variable
    {CIndex K0 K1 Kb Edge : Type*}
    [Fintype CIndex] [DecidableEq CIndex]
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    [DecidableEq Edge]

variable
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCapacity : CIndex → ℕ)
    (allowed0 : CIndex → Finset K0)
    (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ) (base0 : ℕ)
    (A : SourceSegmentAllocation hT P optional S clusterCapacity allowed0
      capacity1 capacityb base0)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)

/-- The literal matching edge assigned to a canonical branch. -/
def coordinateBranchEdge (j : BranchIndex P) : Edge :=
  if _hj0 : j ∈ S.selected then edge0 (A.F0edge j)
  else if _hj1 : j ∈ majorResidualBranches P S then edge1 (A.F1edge j)
  else edgeb (A.Fbedge j)

/-- Coordinate-sensitive root slot of a canonical branch segment. -/
def coordinateBranchRootSlot (j : BranchIndex P) : RootSlot CIndex Edge :=
  if _hj0 : j ∈ S.selected then Sum.inr (Sum.inl (A.F0cluster j))
  else if _hj1 : j ∈ majorResidualBranches P S then
    Sum.inr (Sum.inr ⟨edge1 (A.F1edge j), orient j 0⟩)
  else Sum.inr (Sum.inr ⟨edgeb (A.Fbedge j), orient j 0⟩)

/-- Root pool of every hierarchy segment. -/
def coordinateHierarchyRootSlot (i : SegmentIndex hT P optional) :
    RootSlot CIndex Edge :=
  match segmentSourceClass hT P optional i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j => coordinateBranchRootSlot hT P optional S clusterCapacity
      allowed0 capacity1 capacityb base0 A edge1 edgeb orient j

/-- Pool of an individual hierarchy coordinate.  The online backend consults
this only for non-root coordinates; defining the root value as well makes the
parity/cardinality bridge literal. -/
def coordinateHierarchyInteriorSlot
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    RootSlot CIndex Edge :=
  match hclass : segmentSourceClass hT P optional i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j =>
      let side := orient j (segmentEndpointSide hT P optional i j a)
      if _hj0 : j ∈ S.selected then
        Sum.inr (Sum.inr ⟨edge0 (A.F0edge j), side⟩)
      else if _hj1 : j ∈ majorResidualBranches P S then
        Sum.inr (Sum.inr ⟨edge1 (A.F1edge j), side⟩)
      else Sum.inr (Sum.inr ⟨edgeb (A.Fbedge j), side⟩)

@[simp] theorem coordinateHierarchyRootSlot_branch
    (i : SegmentIndex hT P optional) (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j) :
    coordinateHierarchyRootSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge1 edgeb orient i =
      coordinateBranchRootSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge1 edgeb orient j := by
  simp [coordinateHierarchyRootSlot, hclass]

@[simp] theorem coordinateHierarchyInteriorSlot_branch
    (i : SegmentIndex hT P optional) (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    coordinateHierarchyInteriorSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb orient i a =
      let side := orient j (segmentEndpointSide hT P optional i j a)
      if _hj0 : j ∈ S.selected then
        Sum.inr (Sum.inr ⟨edge0 (A.F0edge j), side⟩)
      else if _hj1 : j ∈ majorResidualBranches P S then
        Sum.inr (Sum.inr ⟨edge1 (A.F1edge j), side⟩)
      else Sum.inr (Sum.inr ⟨edgeb (A.Fbedge j), side⟩) := by
  unfold coordinateHierarchyInteriorSlot
  rw [hclass]

/-- For every non-selected branch-class segment, the coordinate root pool is
the same endpoint selected by local side zero. -/
theorem coordinateRootSlot_eq_interiorSlot_root_of_not_selected
    (hparity : OptionalBranchRootParity P optional)
    (i : SegmentIndex hT P optional) (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j)
    (hj0 : j ∉ S.selected) :
    coordinateHierarchyRootSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge1 edgeb orient i =
      coordinateHierarchyInteriorSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb orient i
          ((AllocationHierarchy hT P optional).segments.root i) := by
  have hside := segmentEndpointSide_root_zero_of_optionalParity
    hT P optional hparity i j hclass
  rw [coordinateHierarchyRootSlot_branch hT P optional S clusterCapacity
      allowed0 capacity1 capacityb base0 A edge1 edgeb orient i j hclass,
    coordinateHierarchyInteriorSlot_branch hT P optional S clusterCapacity
      allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i j hclass]
  by_cases hj1 : j ∈ majorResidualBranches P S <;>
    simp [coordinateBranchRootSlot, hj0, hj1, hside]

end Allocated

end Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout

#print axioms Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout.coordinateRootSlot_eq_interiorSlot_root_of_not_selected
