/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateAllocation
import ErdosProblems.Erdos547b.Claim616HierarchicalCoordinateSourceLayout

/-!
# Canonical endpoint orientations for the coordinate Claim 6.16 layout

This module records the elementary `Fin 2` normalization shared by the
source-facing pair classification and the coordinate-pool load bounds.  A
selected branch is rooted at the endpoint opposite its accessible `C`
cluster, a residual-major branch uses the displayed matching orientation,
and a minor branch is rooted at its prescribed `M_b` side.

There is no host embedding, copy, or continuation premise here.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateOrientation

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim616RichCoordinateAllocation

/-- The unique endpoint equivalence sending local side zero to `side`. -/
def endpointOrientation (side : Fin 2) : Fin 2 ≃ Fin 2 :=
  if side = 0 then Equiv.refl (Fin 2) else Equiv.swap 0 1

@[simp] theorem endpointOrientation_zero (side : Fin 2) :
    endpointOrientation side 0 = side := by
  fin_cases side <;> rfl

@[simp] theorem endpointOrientation_apply (side localSide : Fin 2) :
    endpointOrientation side localSide = orientedSide side localSide := by
  fin_cases side <;> fin_cases localSide <;> rfl

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

variable {B : Type*} {K : Type v}
variable [Fintype B] [DecidableEq B] [Fintype K] [DecidableEq K]
variable (G : SimpleGraph B) [DecidableRel G.Adj]
variable (cluster : K → Finset B) (epsilon density : ℚ)
variable [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon density) L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (C : Finset K)

private abbrev orientationMoutEdges :=
  (MatchingDecomposition.Mout
    (R := regularityReducedGraph G cluster epsilon density) D).edgeSet.toFinite.toFinset

private abbrev orientationW :=
  MatchingDecomposition.V2
      (R := regularityReducedGraph G cluster epsilon density) D ∩
    (matchingSupport (MatchingDecomposition.Mout
        (R := regularityReducedGraph G cluster epsilon density) D) \
      matchingSupport (MatchingDecomposition.Mb
        (R := regularityReducedGraph G cluster epsilon density) D))

private abbrev orientationAllowed0 (i : Fin C.card) :=
  indexedAllowedEdges (regularityReducedGraph G cluster epsilon density)
    (orientationMoutEdges G cluster epsilon density D)
    matchingEdgeEndpoint C (orientationW G cluster epsilon density D) i

/-- The canonical source-facing endpoint orientation of every branch.

Selected branches use the actual indexed access side.  Residual-major
branches retain the displayed endpoint numbering.  Minor branches use the
prescribed `M_b` root side. -/
def canonicalCoordinateOrientation
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (orientationAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2) :
    BranchIndex P → Fin 2 ≃ Fin 2 := fun j ↦
  if _hj0 : j ∈ S.selected then
    endpointOrientation
      (indexedAccessSide (regularityReducedGraph G cluster epsilon density)
        (orientationMoutEdges G cluster epsilon density D)
        matchingEdgeEndpoint C (orientationW G cluster epsilon density D)
        (Aalloc.F0cluster j) (Aalloc.F0edge j))
  else if _hj1 : j ∈ majorResidualBranches P S then
    Equiv.refl (Fin 2)
  else endpointOrientation (mbSide (Aalloc.Fbedge j))

@[simp] theorem canonicalCoordinateOrientation_selected_apply
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (orientationAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (j : BranchIndex P) (hj : j ∈ S.selected) (localSide : Fin 2) :
    canonicalCoordinateOrientation G cluster epsilon density D C hT P optional
        S clusterCap base0 base1 baseb Aalloc mbSide j localSide =
      orientedSide
        (indexedAccessSide (regularityReducedGraph G cluster epsilon density)
          (orientationMoutEdges G cluster epsilon density D)
          matchingEdgeEndpoint C (orientationW G cluster epsilon density D)
          (Aalloc.F0cluster j) (Aalloc.F0edge j)) localSide := by
  simp [canonicalCoordinateOrientation, hj]

@[simp] theorem canonicalCoordinateOrientation_residual_apply
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (orientationAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (j : BranchIndex P) (hj : j ∈ majorResidualBranches P S)
    (localSide : Fin 2) :
    canonicalCoordinateOrientation G cluster epsilon density D C hT P optional
        S clusterCap base0 base1 baseb Aalloc mbSide j localSide = localSide := by
  have hj0 : j ∉ S.selected := (mem_majorResidualBranches P S j).mp hj |>.2
  simp [canonicalCoordinateOrientation, hj0, hj]

@[simp] theorem canonicalCoordinateOrientation_minor_apply
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (orientationAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (j : BranchIndex P) (hj : j ∈ minorBranches P)
    (localSide : Fin 2) :
    canonicalCoordinateOrientation G cluster epsilon density D C hT P optional
        S clusterCap base0 base1 baseb Aalloc mbSide j localSide =
      orientedSide (mbSide (Aalloc.Fbedge j)) localSide := by
  have hjHalf : j ∉ halfBranches P := by
    intro hjHalf
    exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
      hjHalf hj
  have hj0 : j ∉ S.selected := fun hjSelected ↦
    hjHalf (S.selected_available hjSelected)
  have hj1 : j ∉ majorResidualBranches P S := by
    intro hjResidual
    exact hjHalf ((mem_majorResidualBranches P S j).mp hjResidual).1
  simp [canonicalCoordinateOrientation, hj0, hj1]

@[simp] theorem canonicalCoordinateOrientation_selected_zero
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (orientationAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (j : BranchIndex P) (hj : j ∈ S.selected) :
    canonicalCoordinateOrientation G cluster epsilon density D C hT P optional
        S clusterCap base0 base1 baseb Aalloc mbSide j 0 =
      indexedAccessSide (regularityReducedGraph G cluster epsilon density)
        (orientationMoutEdges G cluster epsilon density D)
        matchingEdgeEndpoint C (orientationW G cluster epsilon density D)
        (Aalloc.F0cluster j) (Aalloc.F0edge j) := by
  rw [canonicalCoordinateOrientation_selected_apply G cluster epsilon density
    D C hT P optional S clusterCap base0 base1 baseb Aalloc mbSide j hj]
  exact orientedSide_zero _

@[simp] theorem canonicalCoordinateOrientation_minor_zero
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (orientationAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (j : BranchIndex P) (hj : j ∈ minorBranches P) :
    canonicalCoordinateOrientation G cluster epsilon density D C hT P optional
        S clusterCap base0 base1 baseb Aalloc mbSide j 0 =
      mbSide (Aalloc.Fbedge j) := by
  rw [canonicalCoordinateOrientation_minor_apply G cluster epsilon density D C
    hT P optional S clusterCap base0 base1 baseb Aalloc mbSide j hj]
  exact orientedSide_zero _

end Erdos547b.ZhaoClaim616CoordinateOrientation

#print axioms Erdos547b.ZhaoClaim616CoordinateOrientation.endpointOrientation_apply
#print axioms Erdos547b.ZhaoClaim616CoordinateOrientation.canonicalCoordinateOrientation_selected_apply
#print axioms Erdos547b.ZhaoClaim616CoordinateOrientation.canonicalCoordinateOrientation_residual_apply
#print axioms Erdos547b.ZhaoClaim616CoordinateOrientation.canonicalCoordinateOrientation_minor_apply
