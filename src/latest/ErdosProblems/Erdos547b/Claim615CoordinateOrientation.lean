/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615HierarchicalCoordinateSourceLayout

/-!
# Canonical endpoint orientations for coordinate Claim 6.15

Each of the three finite source packings comes with a source-facing endpoint
of its assigned matching edge.  This file turns those endpoint choices into
literal equivalences of `Fin 2` and records the three source-family
normalizations used by the pair and load calculations.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615CoordinateOrientation

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation

/-- The unique endpoint permutation sending local side zero to `side`. -/
def endpointOrientation (side : Fin 2) : Fin 2 ≃ Fin 2 :=
  if side = 0 then Equiv.refl (Fin 2) else Equiv.swap 0 1

@[simp] theorem endpointOrientation_zero (side : Fin 2) :
    endpointOrientation side 0 = side := by
  fin_cases side <;> rfl

@[simp] theorem endpointOrientation_one (side : Fin 2) :
    endpointOrientation side 1 = if side = 0 then 1 else 0 := by
  fin_cases side <;> rfl

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

section Allocated

variable
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {K0 K1 Kb : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (rootSide0 : K0 → Fin 2) (rootSide1 : K1 → Fin 2)
    (rootSideb : Kb → Fin 2)

/-- Branchwise orientation induced by the source-facing side of its assigned
packing bin. -/
def canonicalCoordinateOrientation :
    ZhaoClaim615CoordinateSourceAllocation.BranchIndex P → Fin 2 ≃ Fin 2 :=
  fun j ↦
    if _hj0 : j ∈ S.selected then endpointOrientation (rootSide0 (A.F0edge j))
    else if _hj1 : j ∈ majorResidualBranches P S then
      endpointOrientation (rootSide1 (A.F1edge j))
    else endpointOrientation (rootSideb (A.Fbedge j))

@[simp] theorem canonicalCoordinateOrientation_selected_apply
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ S.selected) (c : Fin 2) :
    canonicalCoordinateOrientation P S capacity0 capacity1 capacityb A
        rootSide0 rootSide1 rootSideb j c =
      endpointOrientation (rootSide0 (A.F0edge j)) c := by
  simp [canonicalCoordinateOrientation, hj]

@[simp] theorem canonicalCoordinateOrientation_residual_apply
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ majorResidualBranches P S) (c : Fin 2) :
    canonicalCoordinateOrientation P S capacity0 capacity1 capacityb A
        rootSide0 rootSide1 rootSideb j c =
      endpointOrientation (rootSide1 (A.F1edge j)) c := by
  have hj0 : j ∉ S.selected := (mem_majorResidualBranches P S j).mp hj |>.2
  simp [canonicalCoordinateOrientation, hj0, hj]

@[simp] theorem canonicalCoordinateOrientation_minor_apply
    (havailable : available ⊆ halfBranches P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ minorBranches P) (c : Fin 2) :
    canonicalCoordinateOrientation P S capacity0 capacity1 capacityb A
        rootSide0 rootSide1 rootSideb j c =
      endpointOrientation (rootSideb (A.Fbedge j)) c := by
  have hjHalf : j ∉ halfBranches P := by
    intro hjHalf
    exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
      hjHalf hj
  have hj0 : j ∉ S.selected := fun h ↦
    hjHalf (havailable (S.selected_available h))
  have hj1 : j ∉ majorResidualBranches P S := by
    intro h
    exact hjHalf ((mem_majorResidualBranches P S j).mp h).1
  simp [canonicalCoordinateOrientation, hj0, hj1]

@[simp] theorem canonicalCoordinateOrientation_selected_zero
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ S.selected) :
    canonicalCoordinateOrientation P S capacity0 capacity1 capacityb A
        rootSide0 rootSide1 rootSideb j 0 = rootSide0 (A.F0edge j) := by
  rw [canonicalCoordinateOrientation_selected_apply P S capacity0 capacity1
    capacityb A rootSide0 rootSide1 rootSideb j hj]
  exact endpointOrientation_zero _

@[simp] theorem canonicalCoordinateOrientation_residual_zero
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ majorResidualBranches P S) :
    canonicalCoordinateOrientation P S capacity0 capacity1 capacityb A
        rootSide0 rootSide1 rootSideb j 0 = rootSide1 (A.F1edge j) := by
  rw [canonicalCoordinateOrientation_residual_apply P S capacity0 capacity1
    capacityb A rootSide0 rootSide1 rootSideb j hj]
  exact endpointOrientation_zero _

@[simp] theorem canonicalCoordinateOrientation_minor_zero
    (havailable : available ⊆ halfBranches P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ minorBranches P) :
    canonicalCoordinateOrientation P S capacity0 capacity1 capacityb A
        rootSide0 rootSide1 rootSideb j 0 = rootSideb (A.Fbedge j) := by
  rw [canonicalCoordinateOrientation_minor_apply P S capacity0 capacity1
    capacityb A rootSide0 rootSide1 rootSideb havailable j hj]
  exact endpointOrientation_zero _

end Allocated

end Erdos547b.ZhaoClaim615CoordinateOrientation

#print axioms Erdos547b.ZhaoClaim615CoordinateOrientation.canonicalCoordinateOrientation_selected_apply
#print axioms Erdos547b.ZhaoClaim615CoordinateOrientation.canonicalCoordinateOrientation_residual_apply
#print axioms Erdos547b.ZhaoClaim615CoordinateOrientation.canonicalCoordinateOrientation_minor_apply
