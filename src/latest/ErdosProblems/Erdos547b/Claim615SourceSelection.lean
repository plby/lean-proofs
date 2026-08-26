/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616ResidualAllocation

/-!
# The source selection in Zhao Lemma 6.15

This file contains the source-only part of the two cases in Lemma 6.15.
The forest `F²_a` is the family of branches in the major parity half whose
two colour classes both occupy a non-extreme proportion of the branch.  The
forest `F̃_a` is the family of nontrivial branches in that half.  From a lower
bound on either mass, the finite first-threshold argument selects an actual
root-subforest with the displayed lower bound and with overshoot smaller than
one Zhao component.

There is no host graph, embedding, or containment premise in this module.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615SourceSelection

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoLemma59Part2Full

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

abbrev BranchIndex (P : ZhaoForestPartition T globalRoot small) :=
  Fin (Fintype.card (ChildKey P.orderedForest))

/-- One bipartition class of a canonical root-deleted branch. -/
def branchColourClass
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P)
    (c : Fin 2) : Finset (Fin ((branchForest P).branches.size j)) :=
  Finset.univ.filter fun a =>
    ((branchForest P).branches.isTree j).coloringTwoOfVert
      ((branchForest P).branches.root j) a = c

/-- Zhao's `Ratio`: the proportion of colour zero in a root-deleted tree. -/
def branchRatio
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P) : ℝ :=
  (#(branchColourClass P j 0) : ℝ) /
    ((branchForest P).branches.size j : ℝ)

/-- The literal `F²_a`: balanced branches in the major parity half. -/
def balancedMajorBranches
    (P : ZhaoForestPartition T globalRoot small) (α0 : ℝ) :
    Finset (BranchIndex P) :=
  (halfBranches P).filter fun j =>
    α0 < branchRatio P j ∧ branchRatio P j < 1 - α0

@[simp] theorem mem_balancedMajorBranches
    (P : ZhaoForestPartition T globalRoot small) (α0 : ℝ)
    (j : BranchIndex P) :
    j ∈ balancedMajorBranches P α0 ↔
      j ∈ halfBranches P ∧
      α0 < branchRatio P j ∧ branchRatio P j < 1 - α0 := by
  simp [balancedMajorBranches]

/-- The literal `F̃_a`: branches with at least two vertices in the major
parity half. -/
def nontrivialMajorBranches
    (P : ZhaoForestPartition T globalRoot small) : Finset (BranchIndex P) :=
  (halfBranches P).filter fun j => 2 ≤ (branchForest P).branches.size j

@[simp] theorem mem_nontrivialMajorBranches
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P) :
    j ∈ nontrivialMajorBranches P ↔
      j ∈ halfBranches P ∧ 2 ≤ (branchForest P).branches.size j := by
  rw [nontrivialMajorBranches, Finset.mem_filter]

/-- Total vertex mass of a branch family.  In the paper this is `v(·)` or
`||·||` after the adjacent component roots have been restored. -/
def branchMass (P : ZhaoForestPartition T globalRoot small)
    (s : Finset (BranchIndex P)) : ℕ :=
  ∑ j ∈ s, (branchForest P).branches.size j

/-- The concrete selected root-subforest used in either case of Lemma 6.15.
Unlike the Claim-6.16 selector, size-two branches are permitted. -/
structure SelectedF0
    (P : ZhaoForestPartition T globalRoot small)
    (available : Finset (BranchIndex P)) (target slack : ℕ) where
  selected : Finset (BranchIndex P)
  selected_available : selected ⊆ available
  lower : target ≤ branchMass P selected
  upper : branchMass P selected < target + slack

namespace SelectedF0

variable {P : ZhaoForestPartition T globalRoot small}
  {available : Finset (BranchIndex P)} {target slack : ℕ}

/-- The literal restricted ordered branch forest selected by the certificate. -/
abbrev forest (S : SelectedF0 P available target slack) :=
  OrderedBranchForest.restrict (branchForest P) S.selected

@[simp] theorem edgeDemand_forest
    (S : SelectedF0 P available target slack) :
    OrderedBranchForest.edgeDemand S.forest = branchMass P S.selected := by
  change OrderedBranchForest.edgeDemand
      (OrderedBranchForest.restrict (branchForest P) S.selected) =
    ∑ j ∈ S.selected, (branchForest P).branches.size j
  exact OrderedBranchForest.edgeDemand_restrict (branchForest P) S.selected

theorem lower_edgeDemand (S : SelectedF0 P available target slack) :
    target ≤ OrderedBranchForest.edgeDemand S.forest := by
  rw [S.edgeDemand_forest]
  exact S.lower

theorem upper_edgeDemand (S : SelectedF0 P available target slack) :
    OrderedBranchForest.edgeDemand S.forest < target + slack := by
  rw [S.edgeDemand_forest]
  exact S.upper

end SelectedF0

/-- Finite source selector common to the balanced and non-extreme cases. -/
theorem exists_selectedF0
    (P : ZhaoForestPartition T globalRoot small)
    (available : Finset (BranchIndex P)) (target slack : ℕ)
    (hslack : 0 < slack)
    (hsmall : ∀ j ∈ available, (branchForest P).branches.size j ≤ slack)
    (hmass : target ≤ branchMass P available) :
    Nonempty (SelectedF0 P available target slack) := by
  classical
  have hmass' : target ≤
      ∑ j ∈ available, (branchForest P).branches.size j := by
    change target ≤ branchMass P available
    exact hmass
  obtain ⟨s, hs, hlo, hup⟩ :=
    exists_subset_sum_between_target_and_target_add available
      (branchForest P).branches.size target slack hslack hsmall
      hmass'
  exact ⟨{
    selected := s
    selected_available := hs
    lower := by
      change target ≤ ∑ j ∈ s, (branchForest P).branches.size j
      exact hlo
    upper := by
      change (∑ j ∈ s, (branchForest P).branches.size j) < target + slack
      exact hup
  }⟩

/-- Case 1 of Lemma 6.15: select inside the balanced family `F²_a`. -/
theorem exists_balancedSelectedF0
    (P : ZhaoForestPartition T globalRoot small) (α0 : ℝ)
    (target slack : ℕ) (hslack : 0 < slack)
    (hsmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hmass : target ≤ branchMass P (balancedMajorBranches P α0)) :
    Nonempty (SelectedF0 P (balancedMajorBranches P α0) target slack) :=
  exists_selectedF0 P (balancedMajorBranches P α0) target slack hslack
    (fun j _ => hsmall j) hmass

/-- Case 2 of Lemma 6.15: select inside the nontrivial forest `F̃_a`. -/
theorem exists_nontrivialSelectedF0
    (P : ZhaoForestPartition T globalRoot small)
    (target slack : ℕ) (hslack : 0 < slack)
    (hsmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hmass : target ≤ branchMass P (nontrivialMajorBranches P)) :
    Nonempty (SelectedF0 P (nontrivialMajorBranches P) target slack) :=
  exists_selectedF0 P (nontrivialMajorBranches P) target slack hslack
    (fun j _ => hsmall j) hmass

end Erdos547b.ZhaoClaim615SourceSelection

#print axioms Erdos547b.ZhaoClaim615SourceSelection.exists_balancedSelectedF0
#print axioms Erdos547b.ZhaoClaim615SourceSelection.exists_nontrivialSelectedF0
