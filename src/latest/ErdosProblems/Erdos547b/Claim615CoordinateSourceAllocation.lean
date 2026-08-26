/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615SourceSelection
import ErdosProblems.Erdos547b.Claim616HierarchyClassification
import ErdosProblems.Erdos547b.ForestMatching
import ErdosProblems.Erdos547b.IntegralAverageCapacity

/-!
# Source allocation for the coordinate version of Zhao Lemma 6.15

This file deliberately does not import the older segment-pool layout for
Claim 6.15.  It contains only the three finite source packings needed by the
coordinate-sensitive hierarchy: the exceptional selected family, the
remaining major family, and the minor family.  The three matching types may
later be transported to one physical matching.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615CoordinateSourceAllocation

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ForestMatching
open Erdos547b.ZhaoIntegralAverageCapacity
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim615SourceSelection

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

abbrev BranchIndex (P : ZhaoForestPartition T globalRoot small) :=
  ZhaoClaim615SourceSelection.BranchIndex P

/-- Major branches left after selecting the exceptional root-subforest. -/
def majorResidualBranches
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack) : Finset (BranchIndex P) :=
  halfBranches P \ S.selected

@[simp] theorem mem_majorResidualBranches
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack) (j : BranchIndex P) :
    j ∈ majorResidualBranches P S ↔
      j ∈ halfBranches P ∧ j ∉ S.selected := by
  simp [majorResidualBranches]

/-- Branch-coherent finite allocation of the three source families. -/
structure SourceAllocation
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    (K0 K1 Kb : Type*)
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ) where
  F0edge : BranchIndex P → K0
  F1edge : BranchIndex P → K1
  Fbedge : BranchIndex P → Kb
  F0_load : ∀ e : K0,
    ∑ j ∈ S.selected.filter (F0edge · = e),
      (branchForest P).branches.size j ≤ capacity0 e
  F1_load : ∀ e : K1,
    ∑ j ∈ (majorResidualBranches P S).filter (F1edge · = e),
      (branchForest P).branches.size j ≤ capacity1 e
  Fb_load : ∀ e : Kb,
    ∑ j ∈ (minorBranches P).filter (Fbedge · = e),
      (branchForest P).branches.size j ≤ capacityb e

/-- The three allocations follow from the literal aggregate packing
budgets and the canonical small-branch bound. -/
theorem exists_sourceAllocation
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    (K0 K1 Kb : Type*)
    [Fintype K0] [DecidableEq K0] [Nonempty K0]
    [Fintype K1] [DecidableEq K1] [Nonempty K1]
    [Fintype Kb] [DecidableEq Kb] [Nonempty Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (hbudget0 : branchMass P S.selected + Fintype.card K0 * small ≤
      ∑ e : K0, capacity0 e)
    (hbudget1 : branchMass P (majorResidualBranches P S) +
        Fintype.card K1 * small ≤ ∑ e : K1, capacity1 e)
    (hbudgetb : branchMass P (minorBranches P) +
        Fintype.card Kb * small ≤ ∑ e : Kb, capacityb e) :
    Nonempty (SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb) := by
  classical
  have hsmall (j : BranchIndex P) :
      (branchForest P).branches.size j ≤ small :=
    canonical_branch_size_le_small P j
  have hbudget0' :
      (∑ j ∈ S.selected, (branchForest P).branches.size j) +
          Fintype.card K0 * small ≤ ∑ e : K0, capacity0 e := by
    change branchMass P S.selected + Fintype.card K0 * small ≤
      ∑ e : K0, capacity0 e
    exact hbudget0
  have hbudget1' :
      (∑ j ∈ majorResidualBranches P S,
          (branchForest P).branches.size j) +
          Fintype.card K1 * small ≤ ∑ e : K1, capacity1 e := by
    change branchMass P (majorResidualBranches P S) +
      Fintype.card K1 * small ≤ ∑ e : K1, capacity1 e
    exact hbudget1
  have hbudgetb' :
      (∑ j ∈ minorBranches P, (branchForest P).branches.size j) +
          Fintype.card Kb * small ≤ ∑ e : Kb, capacityb e := by
    change branchMass P (minorBranches P) + Fintype.card Kb * small ≤
      ∑ e : Kb, capacityb e
    exact hbudgetb
  obtain ⟨f0, hf0⟩ := capacity_packing S.selected
    (branchForest P).branches.size capacity0 small
    (fun j _ ↦ hsmall j) hbudget0'
  obtain ⟨f1, hf1⟩ := capacity_packing (majorResidualBranches P S)
    (branchForest P).branches.size capacity1 small
    (fun j _ ↦ hsmall j) hbudget1'
  obtain ⟨fb, hfb⟩ := capacity_packing (minorBranches P)
    (branchForest P).branches.size capacityb small
    (fun j _ ↦ hsmall j) hbudgetb'
  exact ⟨{
    F0edge := f0
    F1edge := f1
    Fbedge := fb
    F0_load := hf0
    F1_load := hf1
    Fb_load := hfb
  }⟩

/-- The canonical per-bin capacity for one branch family: its total demand
rounded up to the average bin load, plus the one-small-branch insertion
slack. -/
def averageBranchCapacity (demand bins small : ℕ) : ℕ :=
  averageCapacity demand bins + small

/-- Nonempty finite edge families always admit the three Claim-6.15 source
allocations with canonical average capacities.  Thus the aggregate packing
budgets are consequences of integral rounding, rather than hypotheses of the
eventual embedding theorem. -/
theorem exists_sourceAllocation_average
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    (K0 K1 Kb : Type*)
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    (hK0 : 0 < Fintype.card K0)
    (hK1 : 0 < Fintype.card K1)
    (hKb : 0 < Fintype.card Kb) :
    Nonempty (SourceAllocation P S K0 K1 Kb
      (fun _ ↦ averageBranchCapacity (branchMass P S.selected)
        (Fintype.card K0) small)
      (fun _ ↦ averageBranchCapacity
        (branchMass P (majorResidualBranches P S)) (Fintype.card K1) small)
      (fun _ ↦ averageBranchCapacity (branchMass P (minorBranches P))
        (Fintype.card Kb) small)) := by
  letI : Nonempty K0 := Fintype.card_pos_iff.mp hK0
  letI : Nonempty K1 := Fintype.card_pos_iff.mp hK1
  letI : Nonempty Kb := Fintype.card_pos_iff.mp hKb
  apply exists_sourceAllocation P S K0 K1 Kb
  · simpa only [averageBranchCapacity, Finset.sum_const, Nat.nsmul_eq_mul,
      Finset.card_univ, Fintype.card_coe] using
      total_add_slack_le (branchMass P S.selected) (Fintype.card K0) small hK0
  · simpa only [averageBranchCapacity, Finset.sum_const, Nat.nsmul_eq_mul,
      Finset.card_univ, Fintype.card_coe] using
      total_add_slack_le (branchMass P (majorResidualBranches P S))
        (Fintype.card K1) small hK1
  · simpa only [averageBranchCapacity, Finset.sum_const, Nat.nsmul_eq_mul,
      Finset.card_univ, Fintype.card_coe] using
      total_add_slack_le (branchMass P (minorBranches P))
        (Fintype.card Kb) small hKb

/-- A coordinate hierarchy root slot is either one of the two distinguished
reservoirs or one endpoint of a physical matching edge. -/
abbrev RootSlot (Edge : Type*) := Sum (Fin 2) (Edge × Fin 2)

end Erdos547b.ZhaoClaim615CoordinateSourceAllocation

#print axioms Erdos547b.ZhaoClaim615CoordinateSourceAllocation.exists_sourceAllocation
#print axioms Erdos547b.ZhaoClaim615CoordinateSourceAllocation.exists_sourceAllocation_average
