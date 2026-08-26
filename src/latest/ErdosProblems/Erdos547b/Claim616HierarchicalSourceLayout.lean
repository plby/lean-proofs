/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchicalAllocation
import ErdosProblems.Erdos547b.Claim616HierarchyAttachments

/-!
# Concrete source layout for the Claim 6.16 hierarchy

This module turns the branch-coherent source allocation into the tagged
root slots and physical occupancy pools used by the graph-side constructor.
The three matching families are mapped into one common edge type; hence the
online realizer charges genuinely overlapping endpoint clusters to the same
pool rather than merely giving them definitionally different indices.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchicalSourceLayout

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

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- A root reservoir is either the distinguished major/minor reservoir, a
selected `C` cluster, or one oriented endpoint of an original matching
edge. -/
abbrev RootSlot (CIndex Edge : Type*) :=
  Sum (Fin 2) (Sum CIndex (Edge × Fin 2))

/-- Physical collision pools forget the orientation of a matching edge but
retain the two distinguished reservoirs and the selected `C` clusters. -/
abbrev PhysicalPool (CIndex Edge : Type*) :=
  Sum (Fin 2) (Sum CIndex Edge)

def rootSlotPool {CIndex Edge : Type*} :
    RootSlot CIndex Edge → PhysicalPool CIndex Edge
  | Sum.inl side => Sum.inl side
  | Sum.inr (Sum.inl C0) => Sum.inr (Sum.inl C0)
  | Sum.inr (Sum.inr ⟨e, _side⟩) => Sum.inr (Sum.inr e)

/-- Transport a parity side through an orientation of a matching edge. -/
def orientedSide (rootSide localSide : Fin 2) : Fin 2 :=
  if localSide = 0 then rootSide else if rootSide = 0 then 1 else 0

@[simp] theorem orientedSide_zero (rootSide : Fin 2) :
    orientedSide rootSide 0 = rootSide := by
  simp [orientedSide]

@[simp] theorem orientedSide_one (rootSide : Fin 2) :
    orientedSide rootSide 1 = (if rootSide = 0 then 1 else 0) := by
  simp [orientedSide]

theorem orientedSide_ne_of_ne {rootSide a b : Fin 2} (hab : a ≠ b) :
    orientedSide rootSide a ≠ orientedSide rootSide b := by
  fin_cases rootSide <;> fin_cases a <;> fin_cases b <;>
    simp [orientedSide] at hab ⊢

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
    (accessSide : CIndex → K0 → Fin 2)
    (rootSide1 : K1 → Fin 2) (rootSideb : Kb → Fin 2)

/-- Common physical matching edge inherited by one canonical source branch. -/
def branchEdge (j : BranchIndex P) : Edge :=
  if _hj0 : j ∈ S.selected then edge0 (A.F0edge j)
  else if _hj1 : j ∈ majorResidualBranches P S then edge1 (A.F1edge j)
  else edgeb (A.Fbedge j)

/-- Root slot inherited by every hierarchy segment cut from one canonical
source branch.  `F₀` roots use their assigned C cluster; residual roots use
the source-facing endpoint of their assigned matching edge. -/
def branchRootSlot (j : BranchIndex P) : RootSlot CIndex Edge :=
  if _hj0 : j ∈ S.selected then Sum.inr (Sum.inl (A.F0cluster j))
  else if _hj1 : j ∈ majorResidualBranches P S then
    Sum.inr (Sum.inr ⟨edge1 (A.F1edge j), rootSide1 (A.F1edge j)⟩)
  else
    Sum.inr (Sum.inr ⟨edgeb (A.Fbedge j), rootSideb (A.Fbedge j)⟩)

/-- Root slot of every segment in the strengthened whole-tree hierarchy. -/
def hierarchyRootSlot (i : SegmentIndex hT P optional) :
    RootSlot CIndex Edge :=
  match segmentSourceClass hT P optional i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j => branchRootSlot hT P optional S clusterCapacity allowed0
      capacity1 capacityb base0 A edge1 edgeb rootSide1 rootSideb j

/-- Physical pool charged by a hierarchy segment root. -/
def hierarchyRootPool (i : SegmentIndex hT P optional) :
    PhysicalPool CIndex Edge :=
  rootSlotPool (hierarchyRootSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge1 edgeb rootSide1 rootSideb i)

/-- Physical pool charged by every non-root coordinate of a segment.  Root
class segments are singletons, so their second clause is never used by a
genuine interior vertex. -/
def hierarchyInteriorPool (i : SegmentIndex hT P optional) :
    PhysicalPool CIndex Edge :=
  match segmentSourceClass hT P optional i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j => Sum.inr (Sum.inr
      (branchEdge hT P optional S clusterCapacity allowed0 capacity1
        capacityb base0 A edge0 edge1 edgeb j))

/-- Oriented matching endpoint occupied by a non-root coordinate.  In `F₀`
local side one is the endpoint adjacent to `C`, while local side zero is its
mate.  In `F₁/F_b` local side zero is the selected source-facing side. -/
def hierarchyInteriorSlot
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    RootSlot CIndex Edge :=
  match hclass : segmentSourceClass hT P optional i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j =>
      let localSide := segmentEndpointSide hT P optional i j a
      if _hj0 : j ∈ S.selected then
        Sum.inr (Sum.inr
          ⟨edge0 (A.F0edge j), orientedSide
            (accessSide (A.F0cluster j) (A.F0edge j)) localSide⟩)
      else if _hj1 : j ∈ majorResidualBranches P S then
        Sum.inr (Sum.inr
          ⟨edge1 (A.F1edge j), orientedSide (rootSide1 (A.F1edge j)) localSide⟩)
      else
        Sum.inr (Sum.inr
          ⟨edgeb (A.Fbedge j), orientedSide (rootSideb (A.Fbedge j)) localSide⟩)

@[simp] theorem rootSlotPool_hierarchyInteriorSlot
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    rootSlotPool (hierarchyInteriorSlot hT P optional S clusterCapacity allowed0
      capacity1 capacityb base0 A edge0 edge1 edgeb accessSide rootSide1
      rootSideb i a) =
      hierarchyInteriorPool hT P optional S clusterCapacity allowed0 capacity1
        capacityb base0 A edge0 edge1 edgeb i := by
  unfold hierarchyInteriorSlot hierarchyInteriorPool
  split
  · rename_i q hclass
    simp [hierarchyInteriorPool, hclass, rootSlotPool]
  · rename_i j hclass
    by_cases hj0 : j ∈ S.selected
    · simp [hierarchyInteriorPool, hclass, rootSlotPool, branchEdge, hj0]
    · by_cases hj1 : j ∈ halfBranches P
      · simp [hierarchyInteriorPool, hclass, rootSlotPool, branchEdge, hj0, hj1,
          majorResidualBranches]
      · simp [hierarchyInteriorPool, hclass, rootSlotPool, branchEdge, hj0, hj1,
          majorResidualBranches]

end Allocated

end Erdos547b.ZhaoClaim616HierarchicalSourceLayout

#print axioms Erdos547b.ZhaoClaim616HierarchicalSourceLayout.orientedSide_ne_of_ne
