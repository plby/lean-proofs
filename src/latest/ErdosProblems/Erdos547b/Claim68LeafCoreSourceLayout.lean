/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68LeafCoreClassification
import ErdosProblems.Erdos547b.Claim616HierarchicalSourceLayout

/-!
# Concrete source slots for the Claim 6.8 leaf core

The branch-coherent allocation used for the whole Zhao tree is made on the
original canonical branches.  Deleting the original level-one leaves only
removes source vertices, so every surviving leaf-core segment inherits the
same selected cluster or original matching edge as its original branch.

This file supplies that inherited slot layout.  It is entirely source-side:
there is no host copy, candidate-degree assumption, or continuation premise.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim68LeafCoreSourceLayout

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim68HierarchicalLeaves
open Erdos547b.ZhaoClaim68LeafCoreClassification
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- Original-tree parity side occupied by one coordinate of a leaf-core
segment of canonical branch class `j`. -/
def leafSegmentEndpointSide
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (i : LeafSegmentIndex P hT) (j : BranchIndex P)
    (a : Fin ((leafAllocationHierarchy P hT).segments.size i)) : Fin 2 :=
  canonicalBranchSide P j
    ((wholeHierarchyOriginalVertex (leafDeletedCore P)
      (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
      (leafAllocationSpecial P hT) (Sum.inr ⟨i, a⟩)).1)

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
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCapacity : CIndex → ℕ)
    (allowed0 : CIndex → Finset K0)
    (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ) (base0 : ℕ)
    (A : SourceSegmentAllocation hT P ∅ S clusterCapacity allowed0
      capacity1 capacityb base0)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (accessSide : CIndex → K0 → Fin 2)
    (rootSide1 : K1 → Fin 2) (rootSideb : Kb → Fin 2)

/-- Common physical matching edge inherited by one surviving canonical
branch. -/
def leafBranchEdge (j : BranchIndex P) : Edge :=
  if _hj0 : j ∈ S.selected then edge0 (A.F0edge j)
  else if _hj1 : j ∈ majorResidualBranches P S then edge1 (A.F1edge j)
  else edgeb (A.Fbedge j)

/-- Root slot inherited by a surviving branch-class segment. -/
def leafBranchRootSlot (j : BranchIndex P) : RootSlot CIndex Edge :=
  if _hj0 : j ∈ S.selected then Sum.inr (Sum.inl (A.F0cluster j))
  else if _hj1 : j ∈ majorResidualBranches P S then
    Sum.inr (Sum.inr ⟨edge1 (A.F1edge j), rootSide1 (A.F1edge j)⟩)
  else
    Sum.inr (Sum.inr ⟨edgeb (A.Fbedge j), rootSideb (A.Fbedge j)⟩)

/-- Root slot of every leaf-core hierarchy segment. -/
def leafHierarchyRootSlot (i : LeafSegmentIndex P hT) :
    RootSlot CIndex Edge :=
  match leafSegmentSourceClass P hT i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j => leafBranchRootSlot hT P S clusterCapacity allowed0
      capacity1 capacityb base0 A edge1 edgeb rootSide1 rootSideb j

/-- Physical pool charged by a leaf-core segment root. -/
def leafHierarchyRootPool (i : LeafSegmentIndex P hT) :
    PhysicalPool CIndex Edge :=
  rootSlotPool (leafHierarchyRootSlot hT P S clusterCapacity allowed0
    capacity1 capacityb base0 A edge1 edgeb rootSide1 rootSideb i)

/-- Physical pool charged by every non-root coordinate of a leaf-core
segment. -/
def leafHierarchyInteriorPool (i : LeafSegmentIndex P hT) :
    PhysicalPool CIndex Edge :=
  match leafSegmentSourceClass P hT i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j => Sum.inr (Sum.inr
      (leafBranchEdge hT P S clusterCapacity allowed0 capacity1 capacityb
        base0 A edge0 edge1 edgeb j))

/-- Oriented endpoint occupied by one coordinate of a leaf-core segment. -/
def leafHierarchyInteriorSlot
    (i : LeafSegmentIndex P hT)
    (a : Fin ((leafAllocationHierarchy P hT).segments.size i)) :
    RootSlot CIndex Edge :=
  match hclass : leafSegmentSourceClass P hT i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j =>
      let local := leafSegmentEndpointSide P hT i j a
      if _hj0 : j ∈ S.selected then
        Sum.inr (Sum.inr
          ⟨edge0 (A.F0edge j), orientedSide
            (accessSide (A.F0cluster j) (A.F0edge j)) local⟩)
      else if _hj1 : j ∈ majorResidualBranches P S then
        Sum.inr (Sum.inr
          ⟨edge1 (A.F1edge j), orientedSide (rootSide1 (A.F1edge j)) local⟩)
      else
        Sum.inr (Sum.inr
          ⟨edgeb (A.Fbedge j), orientedSide (rootSideb (A.Fbedge j)) local⟩)

@[simp] theorem rootSlotPool_leafHierarchyInteriorSlot
    (i : LeafSegmentIndex P hT)
    (a : Fin ((leafAllocationHierarchy P hT).segments.size i)) :
    rootSlotPool (leafHierarchyInteriorSlot hT P S clusterCapacity allowed0
      capacity1 capacityb base0 A edge0 edge1 edgeb accessSide rootSide1
      rootSideb i a) =
      leafHierarchyInteriorPool hT P S clusterCapacity allowed0 capacity1
        capacityb base0 A edge0 edge1 edgeb i := by
  cases hclass : leafSegmentSourceClass P hT i with
  | inl q =>
      simp [leafHierarchyInteriorSlot, leafHierarchyInteriorPool, hclass]
  | inr j =>
      by_cases hj0 : j ∈ S.selected
      · simp [leafHierarchyInteriorSlot, leafHierarchyInteriorPool,
          leafBranchEdge, hclass, hj0]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · simp [leafHierarchyInteriorSlot, leafHierarchyInteriorPool,
            leafBranchEdge, hclass, hj0, hj1]
        · simp [leafHierarchyInteriorSlot, leafHierarchyInteriorPool,
            leafBranchEdge, hclass, hj0, hj1]

/-- The physical-pool equality required by the one-shot hierarchy
constructor. -/
theorem leafHierarchyInteriorSlot_pool_eq_root
    (i : LeafSegmentIndex P hT)
    (a : Fin ((leafAllocationHierarchy P hT).segments.size i)) :
    rootSlotPool (leafHierarchyInteriorSlot hT P S clusterCapacity allowed0
      capacity1 capacityb base0 A edge0 edge1 edgeb accessSide rootSide1
      rootSideb i a) =
    rootSlotPool (leafHierarchyInteriorSlot hT P S clusterCapacity allowed0
      capacity1 capacityb base0 A edge0 edge1 edgeb accessSide rootSide1
      rootSideb i ((leafAllocationHierarchy P hT).segments.root i)) := by
  rw [rootSlotPool_leafHierarchyInteriorSlot,
    rootSlotPool_leafHierarchyInteriorSlot]

end Allocated

end Erdos547b.ZhaoClaim68LeafCoreSourceLayout

#print axioms Erdos547b.ZhaoClaim68LeafCoreSourceLayout.rootSlotPool_leafHierarchyInteriorSlot
