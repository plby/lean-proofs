/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateRootWeight

/-!
# Source allocation with canonical hierarchy-root bounds

This wrapper removes the proof-valued per-branch root-weight premise from the
Claim 6.16 source allocator.  The only remaining level-zero input is the
literal aggregate scalar budget obtained by charging `small` once for every
selected branch and once for every target cluster.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateSourceAllocation

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616CoordinateRootWeight

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- The selection certificate itself bounds the number of selected branches
by its displayed target window.  (In fact the large-branch condition gives
the stronger factor-three inequality.) -/
theorem selected_card_le_target_add
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    #S.selected ≤ target + slack := by
  have hthree := S.toSelectedF0.three_mul_levelOne_le_edgeDemand
  have hupper := S.upper
  simp only [SelectedF0.forest, OrderedBranchForest.levelOneDemand_restrict]
    at hthree
  omega

/-- Canonical-root specialization of `exists_sourceSegmentAllocation`.
Every selected hierarchy-root weight is bounded internally by `small`. -/
theorem exists_sourceSegmentAllocation_smallRoot
    {CIndex K0 K1 Kb : Type*}
    [Fintype CIndex] [DecidableEq CIndex] [Nonempty CIndex]
    [Fintype K0] [DecidableEq K0] [Nonempty K0]
    [Fintype K1] [DecidableEq K1] [Nonempty K1]
    [Fintype Kb] [DecidableEq Kb] [Nonempty Kb]
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCapacity : CIndex → ℕ)
    (allowed0 : CIndex → Finset K0)
    (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ)
    (m0 base0 : ℕ)
    (hm0 : 0 < m0)
    (hlevel0 : #S.selected * small + Fintype.card CIndex * small ≤
      ∑ C0 : CIndex, clusterCapacity C0)
    (hallowed0 : ∀ C0, m0 ≤ #(allowed0 C0))
    (hbudget0 : (∑ j ∈ S.selected,
        ((branchForest P).branches.size j - 1)) ≤ m0 * base0)
    (hbudget1 : OrderedBranchForest.edgeDemand (F1 P S) +
        Fintype.card K1 * small ≤ ∑ e : K1, capacity1 e)
    (hbudgetb : OrderedBranchForest.edgeDemand (Fb P) +
        Fintype.card Kb * small ≤ ∑ e : Kb, capacityb e) :
    Nonempty (SourceSegmentAllocation hT P optional S
      clusterCapacity allowed0 capacity1 capacityb base0) := by
  apply exists_sourceSegmentAllocation hT P optional S clusterCapacity
    allowed0 capacity1 capacityb m0 base0 small hm0
  · intro j _hj
    exact F0segmentRootWeight_le_small hT P optional S j
  · exact (Nat.add_le_add_right
      (sum_F0segmentRootWeight_le_card_mul_small hT P optional S)
      (Fintype.card CIndex * small)).trans hlevel0
  · exact hallowed0
  · exact hbudget0
  · exact hbudget1
  · exact hbudgetb

/-- A target-window version of the preceding allocator.  It is often the
most convenient eventual-arithmetic interface: the selected-family cardinal
has disappeared, leaving only `target`, `slack`, and the number of target
clusters. -/
theorem exists_sourceSegmentAllocation_targetLevel
    {CIndex K0 K1 Kb : Type*}
    [Fintype CIndex] [DecidableEq CIndex] [Nonempty CIndex]
    [Fintype K0] [DecidableEq K0] [Nonempty K0]
    [Fintype K1] [DecidableEq K1] [Nonempty K1]
    [Fintype Kb] [DecidableEq Kb] [Nonempty Kb]
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCapacity : CIndex → ℕ)
    (allowed0 : CIndex → Finset K0)
    (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ)
    (m0 base0 : ℕ)
    (hm0 : 0 < m0)
    (hlevel0 : (target + slack) * small +
        Fintype.card CIndex * small ≤
      ∑ C0 : CIndex, clusterCapacity C0)
    (hallowed0 : ∀ C0, m0 ≤ #(allowed0 C0))
    (hbudget0 : (∑ j ∈ S.selected,
        ((branchForest P).branches.size j - 1)) ≤ m0 * base0)
    (hbudget1 : OrderedBranchForest.edgeDemand (F1 P S) +
        Fintype.card K1 * small ≤ ∑ e : K1, capacity1 e)
    (hbudgetb : OrderedBranchForest.edgeDemand (Fb P) +
        Fintype.card Kb * small ≤ ∑ e : Kb, capacityb e) :
    Nonempty (SourceSegmentAllocation hT P optional S
      clusterCapacity allowed0 capacity1 capacityb base0) := by
  apply exists_sourceSegmentAllocation_smallRoot hT P optional S
    clusterCapacity allowed0 capacity1 capacityb m0 base0 hm0
  · exact (Nat.add_le_add_right
      (Nat.mul_le_mul_right small (selected_card_le_target_add P S))
      (Fintype.card CIndex * small)).trans hlevel0
  · exact hallowed0
  · exact hbudget0
  · exact hbudget1
  · exact hbudgetb

end Erdos547b.ZhaoClaim616CoordinateSourceAllocation

#print axioms Erdos547b.ZhaoClaim616CoordinateSourceAllocation.exists_sourceSegmentAllocation_smallRoot
#print axioms Erdos547b.ZhaoClaim616CoordinateSourceAllocation.exists_sourceSegmentAllocation_targetLevel
