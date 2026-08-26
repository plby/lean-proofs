/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichHierarchicalAllocation
import ErdosProblems.Erdos547b.Claim615CoordinateOrientation

/-!
# Concrete physical matching families for Zhao Claim 6.15

This module combines the independently selected exceptional and reserved
families with the positive-contribution remainder.  It supplies literal
finite bin types, physical edge maps, source-facing endpoint choices, and a
canonical average-capacity source allocation.  No embedding or containment
datum occurs here.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615CoordinateOrientation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable {Pcluster : ClusterAssignment Bv I}
variable {Gdegree : SimpleGraph Bv} [DecidableRel Gdegree.Adj]
variable {threshold quota : ℕ} {R : SimpleGraph I} [DecidableRel R.Adj]
variable {miss : ℕ}
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (sourceDensity : EvenPadding I → EvenPadding I → ℝ)

section Families

variable {L : Finset (EvenPadding I)} {eta N targetB cap : ℝ}
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

/-- Exceptional bins selected for the first root-subforest. -/
abbrev K0 := E0.IndexedEdge

/-- Positive `A`-contribution bins left after deleting `M₀ ∪ M_b`. -/
abbrev K1 := PositiveRemainingEdgesA.IndexedEdge
  (Q := Q) (density := sourceDensity) (L := L) (N := N)
  (forbidden := E0.selected ∪ Mb.selected)

/-- The independently reserved `B`-bins. -/
abbrev Kb := {e : MatchingEdge Q.claim67.M // e ∈ Mb.selected}

def edge0 (e : K0 Q sourceDensity E0) : MatchingEdge Q.claim67.M :=
  SelectedExceptionalEdges.edge Q sourceDensity E0 e

def edge1 (e : K1 Q sourceDensity E0 Mb) : MatchingEdge Q.claim67.M := e.1

def edgeb (e : Kb Q sourceDensity Mb) : MatchingEdge Q.claim67.M := e.1

def rootSide0 (e : K0 Q sourceDensity E0) : Fin 2 :=
  SelectedExceptionalEdges.rootSide Q sourceDensity E0 e

def rootSide1 (e : K1 Q sourceDensity E0 Mb) : Fin 2 :=
  PositiveRemainingEdgesA.rootSide Q sourceDensity e

def rootSideb (e : Kb Q sourceDensity Mb) : Fin 2 :=
  PreliminaryReservedEdges.rootSide Q sourceDensity Mb e

theorem edge0_injective : Function.Injective (edge0 Q sourceDensity E0) :=
  (SelectedExceptionalEdges.edge_injective Q sourceDensity E0)

theorem edge1_injective : Function.Injective (edge1 Q sourceDensity E0 Mb) := by
  intro e f hef
  exact Subtype.ext hef

theorem edgeb_injective : Function.Injective (edgeb Q sourceDensity Mb) := by
  intro e f hef
  exact Subtype.ext hef

/-- The remaining family is physically disjoint from both earlier families. -/
theorem edge1_ne_edge0
    (e1 : K1 Q sourceDensity E0 Mb) (e0 : K0 Q sourceDensity E0) :
    edge1 Q sourceDensity E0 Mb e1 ≠ edge0 Q sourceDensity E0 e0 := by
  intro heq
  have hnot := PositiveRemainingEdgesA.edge_not_mem_forbidden
    Q sourceDensity e1
  change edge1 Q sourceDensity E0 Mb e1 ∉ E0.selected ∪ Mb.selected at hnot
  apply hnot
  rw [heq, Finset.mem_union]
  exact Or.inl (SelectedExceptionalEdges.edge_mem Q sourceDensity E0 e0)

theorem edge1_ne_edgeb
    (e1 : K1 Q sourceDensity E0 Mb) (eb : Kb Q sourceDensity Mb) :
    edge1 Q sourceDensity E0 Mb e1 ≠ edgeb Q sourceDensity Mb eb := by
  intro heq
  have hnot := PositiveRemainingEdgesA.edge_not_mem_forbidden
    Q sourceDensity e1
  change edge1 Q sourceDensity E0 Mb e1 ∉ E0.selected ∪ Mb.selected at hnot
  apply hnot
  rw [heq, Finset.mem_union]
  exact Or.inr eb.2

theorem edge0_ne_edgeb
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (e0 : K0 Q sourceDensity E0) (eb : Kb Q sourceDensity Mb) :
    edge0 Q sourceDensity E0 e0 ≠ edgeb Q sourceDensity Mb eb := by
  intro heq
  apply Finset.disjoint_left.mp hdisjoint
    (SelectedExceptionalEdges.edge_mem Q sourceDensity E0 e0)
  change edge0 Q sourceDensity E0 e0 ∈ Mb.selected
  rw [heq]
  exact eb.2

theorem rootSide0_adj_A
    (heta : 0 < eta)
    (hrow : ∀ x, 0 ≤ sourceDensity (Sum.inl Q.A) x)
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x)
    (e : K0 Q sourceDensity E0) :
    (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 Q sourceDensity E0 e).1
        (rootSide0 Q sourceDensity E0 e)) :=
  SelectedExceptionalEdges.rootSide_adj_A Q sourceDensity E0 heta hrow hAdj e

theorem rootSide1_adj_A
    (hN : 0 < N)
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x)
    (e : K1 Q sourceDensity E0 Mb) :
    (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge1 Q sourceDensity E0 Mb e).1
        (rootSide1 Q sourceDensity E0 Mb e)) :=
  PositiveRemainingEdgesA.rootSide_adj_A Q sourceDensity hN hAdj e

theorem rootSideb_adj_B
    (hN : 0 < N)
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.B) x →
      (padGraph R).Adj (Sum.inl Q.B) x)
    (e : Kb Q sourceDensity Mb) :
    (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb Q sourceDensity Mb e).1
        (rootSideb Q sourceDensity Mb e)) :=
  PreliminaryReservedEdges.rootSide_adj_B Q sourceDensity Mb hN hAdj e

end Families

section Allocation

variable (P : ZhaoForestPartition T globalRoot small)
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)} {target slack : ℕ}
variable (S : SelectedF0 P available target slack)
variable {L : Finset (EvenPadding I)} {eta N targetB cap : ℝ}
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

def capacity0 : K0 Q sourceDensity E0 → ℕ := fun _ ↦
  averageBranchCapacity (branchMass P S.selected)
    (Fintype.card (K0 Q sourceDensity E0)) small

def capacity1 : K1 Q sourceDensity E0 Mb → ℕ := fun _ ↦
  averageBranchCapacity (branchMass P (majorResidualBranches P S))
    (Fintype.card (K1 Q sourceDensity E0 Mb)) small

def capacityb : Kb Q sourceDensity Mb → ℕ := fun _ ↦
  averageBranchCapacity (branchMass P (minorBranches P))
    (Fintype.card (Kb Q sourceDensity Mb)) small

/-- A physical-family allocation with honest edge-dependent capacities. -/
abbrev PhysicalSourceAllocationWith
    (capacity0 : K0 Q sourceDensity E0 → ℕ)
    (capacity1 : K1 Q sourceDensity E0 Mb → ℕ)
    (capacityb : Kb Q sourceDensity Mb → ℕ) := SourceAllocation P S
  (K0 Q sourceDensity E0) (K1 Q sourceDensity E0 Mb)
  (Kb Q sourceDensity Mb)
  capacity0 capacity1 capacityb

/-- The earlier constant-average specialization.  It is useful for pure
packing arithmetic, but host-feasible Claim-6.15 applications use
`PhysicalSourceAllocationWith` with source-density capacities. -/
abbrev PhysicalSourceAllocation := PhysicalSourceAllocationWith
  Q sourceDensity P S E0 Mb
  (capacity0 Q sourceDensity P S E0)
  (capacity1 Q sourceDensity P S E0 Mb)
  (capacityb Q sourceDensity P Mb)

/-- The three literal physical families admit the canonical integral source
packing as soon as their three mathematically necessary nonemptiness facts
hold. -/
theorem exists_sourceAllocation_average_physical
    (hcount : 0 < count) (htargetB : 0 < targetB)
    (hnonnegA : ∀ e ∈ allMatchingEdges Q.claim67.M,
      0 ≤ N * (sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 0) +
        sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 1)))
    (hremainingA : 0 < sourceDegree Q.claim67.M L sourceDensity N
      (Sum.inl Q.A) (allMatchingEdges Q.claim67.M \
        (E0.selected ∪ Mb.selected))) :
    Nonempty (PhysicalSourceAllocation Q sourceDensity P S E0 Mb) := by
  have hK0 : 0 < Fintype.card (K0 Q sourceDensity E0) := by
    simpa [K0, E0.selected_card] using hcount
  have hK1Nonempty := positiveRemainingEdgesA_nonempty Q sourceDensity L N
    (E0.selected ∪ Mb.selected) hnonnegA hremainingA
  have hK1 : 0 < Fintype.card (K1 Q sourceDensity E0 Mb) := by
    rw [Fintype.card_pos_iff]
    obtain ⟨e, he⟩ := hK1Nonempty
    exact ⟨⟨e, he⟩⟩
  have hKbNonempty := PreliminaryReservedEdges.selected_nonempty
    Q sourceDensity Mb htargetB
  have hKb : 0 < Fintype.card (Kb Q sourceDensity Mb) := by
    rw [Fintype.card_pos_iff]
    obtain ⟨e, he⟩ := hKbNonempty
    exact ⟨⟨e, he⟩⟩
  change Nonempty (SourceAllocation P S
    (K0 Q sourceDensity E0) (K1 Q sourceDensity E0 Mb)
    (Kb Q sourceDensity Mb)
    (fun _ ↦ averageBranchCapacity (branchMass P S.selected)
      (Fintype.card (K0 Q sourceDensity E0)) small)
    (fun _ ↦ averageBranchCapacity
      (branchMass P (majorResidualBranches P S))
      (Fintype.card (K1 Q sourceDensity E0 Mb)) small)
    (fun _ ↦ averageBranchCapacity (branchMass P (minorBranches P))
      (Fintype.card (Kb Q sourceDensity Mb)) small))
  exact exists_sourceAllocation_average P S
    (K0 Q sourceDensity E0) (K1 Q sourceDensity E0 Mb)
    (Kb Q sourceDensity Mb) hK0 hK1 hKb

/-- Canonical branch orientation induced by the three concrete physical
families and one actual source allocation. -/
def orientation
    (A : PhysicalSourceAllocation Q sourceDensity P S E0 Mb) :
    ZhaoClaim615CoordinateSourceAllocation.BranchIndex P → Fin 2 ≃ Fin 2 :=
  canonicalCoordinateOrientation P S
    (capacity0 Q sourceDensity P S E0)
    (capacity1 Q sourceDensity P S E0 Mb)
    (capacityb Q sourceDensity P Mb) A
    (rootSide0 Q sourceDensity E0)
    (rootSide1 Q sourceDensity E0 Mb)
    (rootSideb Q sourceDensity Mb)

theorem assignedRoot0_adj_A
    (A : PhysicalSourceAllocation Q sourceDensity P S E0 Mb)
    (heta : 0 < eta)
    (hrow : ∀ x, 0 ≤ sourceDensity (Sum.inl Q.A) x)
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ S.selected) :
    (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint
        (edge0 Q sourceDensity E0 (A.F0edge j)).1
        (orientation Q sourceDensity P S E0 Mb A j 0)) := by
  rw [orientation]
  rw [canonicalCoordinateOrientation_selected_zero P S
    (capacity0 Q sourceDensity P S E0)
    (capacity1 Q sourceDensity P S E0 Mb)
    (capacityb Q sourceDensity P Mb) A
    (rootSide0 Q sourceDensity E0)
    (rootSide1 Q sourceDensity E0 Mb)
    (rootSideb Q sourceDensity Mb) j hj]
  exact rootSide0_adj_A Q sourceDensity E0 heta hrow hAdj (A.F0edge j)

theorem assignedRoot1_adj_A
    (A : PhysicalSourceAllocation Q sourceDensity P S E0 Mb)
    (hN : 0 < N)
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ majorResidualBranches P S) :
    (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint
        (edge1 Q sourceDensity E0 Mb (A.F1edge j)).1
        (orientation Q sourceDensity P S E0 Mb A j 0)) := by
  rw [orientation]
  rw [canonicalCoordinateOrientation_residual_zero P S
    (capacity0 Q sourceDensity P S E0)
    (capacity1 Q sourceDensity P S E0 Mb)
    (capacityb Q sourceDensity P Mb) A
    (rootSide0 Q sourceDensity E0)
    (rootSide1 Q sourceDensity E0 Mb)
    (rootSideb Q sourceDensity Mb) j hj]
  exact rootSide1_adj_A Q sourceDensity E0 Mb hN hAdj (A.F1edge j)

theorem assignedRootb_adj_B
    (A : PhysicalSourceAllocation Q sourceDensity P S E0 Mb)
    (havailable : available ⊆ halfBranches P)
    (hN : 0 < N)
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.B) x →
      (padGraph R).Adj (Sum.inl Q.B) x)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ minorBranches P) :
    (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint
        (edgeb Q sourceDensity Mb (A.Fbedge j)).1
        (orientation Q sourceDensity P S E0 Mb A j 0)) := by
  rw [orientation]
  rw [canonicalCoordinateOrientation_minor_zero P S
    (capacity0 Q sourceDensity P S E0)
    (capacity1 Q sourceDensity P S E0 Mb)
    (capacityb Q sourceDensity P Mb) A
    (rootSide0 Q sourceDensity E0)
    (rootSide1 Q sourceDensity E0 Mb)
    (rootSideb Q sourceDensity Mb) havailable j hj]
  exact rootSideb_adj_B Q sourceDensity Mb hN hAdj (A.Fbedge j)

end Allocation

end Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies

#print axioms Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies.edge1_ne_edge0
#print axioms Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies.rootSide0_adj_A
#print axioms Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies.rootSide1_adj_A
#print axioms Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies.rootSideb_adj_B
#print axioms Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies.exists_sourceAllocation_average_physical
#print axioms Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies.assignedRoot0_adj_A
#print axioms Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies.assignedRoot1_adj_A
#print axioms Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies.assignedRootb_adj_B
