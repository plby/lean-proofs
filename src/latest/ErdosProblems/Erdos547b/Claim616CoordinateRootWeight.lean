/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchicalAllocation

/-!
# Canonical bounds for the selected hierarchy root load

The level-zero load in the Claim 6.16 source allocation counts hierarchy
segments whose source is one fixed selected canonical branch.  Every such
segment is nonempty, while the source-class mass injection places all of its
vertices inside that branch.  Consequently the number of segment roots is at
most the branch size, and hence at most the global Zhao component bound.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateRootWeight

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- The segment-root demand carried by one selected canonical branch is at
most the number of vertices in that branch. -/
theorem F0segmentRootWeight_le_branch_size
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) :
    F0segmentRootWeight hT P optional S j ≤
      (branchForest P).branches.size j := by
  classical
  let I := (F0Segments hT P optional S).filter fun i ↦
    segmentSourceClass hT P optional i = Sum.inr j
  have hcard : #I ≤
      ∑ i ∈ I, (AllocationHierarchy hT P optional).segments.size i := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.zero_lt_of_lt
      ((AllocationHierarchy hT P optional).segments.root i).isLt
  have hmass := sum_segmentSize_le_branchMass_of_class hT P optional I {j} (by
    intro i hi a
    have hclass : segmentSourceClass hT P optional i = Sum.inr j :=
      (Finset.mem_filter.mp hi).2
    exact ⟨j, Finset.mem_singleton_self j,
      (wholeSegment_sourceClass_eq_of_boundary hT P optional
        (canonicalWholeSourceBoundary hT P optional) i a).trans hclass⟩)
  change #I ≤ (branchForest P).branches.size j
  exact hcard.trans (by simpa only [Finset.sum_singleton] using hmass)

/-- The global Zhao component bound controls every selected hierarchy
segment-root weight; no separate source-allocation hypothesis is needed. -/
theorem F0segmentRootWeight_le_small
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) :
    F0segmentRootWeight hT P optional S j ≤ small :=
  (F0segmentRootWeight_le_branch_size hT P optional S j).trans
    (canonical_branch_size_le_small P j)

/-- Aggregate form used by the level-zero cluster packing. -/
theorem sum_F0segmentRootWeight_le_card_mul_small
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ j ∈ S.selected, F0segmentRootWeight hT P optional S j) ≤
      #S.selected * small := by
  calc
    (∑ j ∈ S.selected, F0segmentRootWeight hT P optional S j) ≤
        ∑ _j ∈ S.selected, small := by
      apply Finset.sum_le_sum
      intro j _hj
      exact F0segmentRootWeight_le_small hT P optional S j
    _ = #S.selected * small := by simp

end Erdos547b.ZhaoClaim616CoordinateRootWeight

#print axioms Erdos547b.ZhaoClaim616CoordinateRootWeight.F0segmentRootWeight_le_branch_size
#print axioms Erdos547b.ZhaoClaim616CoordinateRootWeight.F0segmentRootWeight_le_small
#print axioms Erdos547b.ZhaoClaim616CoordinateRootWeight.sum_F0segmentRootWeight_le_card_mul_small
