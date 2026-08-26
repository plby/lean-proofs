/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615SourceSelection
import ErdosProblems.Erdos547b.RoundedScales

/-!
# The family-dependent source target in Zhao's Claim 6.15

After the exceptional submatching `E₀` has been chosen, Zhao chooses the
root-subforest `F₀` with

`‖F₀‖ ≥ deg(A, E₀) + η³ n`.

Thus the integral selection threshold depends on `E₀`; it cannot be fixed
before the exceptional family is selected.  This file records the exact
ceiling and the two source selectors used in the unbalanced and nonextreme
branches.  It contains no host graph or embedding premise.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615SourceFamilyTarget

open Finset SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoRoundedScales

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The literal integral threshold selected after the exceptional
submatching.  `exceptionalDegree` denotes `deg(A,E₀)` and `n` is represented
as a real because the reduced-graph degree bookkeeping is real-valued. -/
def exceptionalForestTarget
    (exceptionalDegree eta n : ℝ) : ℕ :=
  upperScale (exceptionalDegree + eta ^ 3 * n)

/-- The selected integer target is at least Zhao's displayed real target. -/
theorem exceptionalForestTarget_lower
    (exceptionalDegree eta n : ℝ) :
    exceptionalDegree + eta ^ 3 * n ≤
      (exceptionalForestTarget exceptionalDegree eta n : ℝ) := by
  exact le_upperScale_cast _

/-- There is less than one vertex of ceiling loss. -/
theorem exceptionalForestTarget_lt_add_one
    {exceptionalDegree eta n : ℝ}
    (hnonneg : 0 ≤ exceptionalDegree + eta ^ 3 * n) :
    (exceptionalForestTarget exceptionalDegree eta n : ℝ) <
      exceptionalDegree + eta ^ 3 * n + 1 := by
  exact upperScale_cast_lt_add_one hnonneg

/-- Generic first-threshold selection with the family-dependent target.
Because the available forest mass is integral, a real upper bound for the
displayed target implies an upper bound for its natural-number ceiling. -/
theorem exists_selectedF0_for_exceptionalDegree
    (P : ZhaoForestPartition T globalRoot small)
    (available : Finset (BranchIndex P))
    (exceptionalDegree eta n : ℝ) (slack : ℕ)
    (hslack : 0 < slack)
    (hsmall : ∀ j ∈ available,
      (branchForest P).branches.size j ≤ slack)
    (hmass : exceptionalDegree + eta ^ 3 * n ≤
      (branchMass P available : ℝ)) :
    Nonempty (SelectedF0 P available
      (exceptionalForestTarget exceptionalDegree eta n) slack) := by
  apply exists_selectedF0 P available
    (exceptionalForestTarget exceptionalDegree eta n) slack hslack hsmall
  rw [exceptionalForestTarget, upperScale]
  exact Nat.ceil_le.mpr hmass

/-- The family-dependent selector for the unbalanced exceptional case. -/
theorem exists_balancedSelectedF0_for_exceptionalDegree
    (P : ZhaoForestPartition T globalRoot small) (ratio : ℝ)
    (exceptionalDegree eta n : ℝ) (slack : ℕ)
    (hslack : 0 < slack)
    (hsmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hmass : exceptionalDegree + eta ^ 3 * n ≤
      (branchMass P (balancedMajorBranches P ratio) : ℝ)) :
    Nonempty (SelectedF0 P (balancedMajorBranches P ratio)
      (exceptionalForestTarget exceptionalDegree eta n) slack) := by
  exact exists_selectedF0_for_exceptionalDegree P
    (balancedMajorBranches P ratio) exceptionalDegree eta n slack hslack
    (fun j _ ↦ hsmall j) hmass

/-- The family-dependent selector for the nonextreme exceptional case. -/
theorem exists_nontrivialSelectedF0_for_exceptionalDegree
    (P : ZhaoForestPartition T globalRoot small)
    (exceptionalDegree eta n : ℝ) (slack : ℕ)
    (hslack : 0 < slack)
    (hsmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hmass : exceptionalDegree + eta ^ 3 * n ≤
      (branchMass P (nontrivialMajorBranches P) : ℝ)) :
    Nonempty (SelectedF0 P (nontrivialMajorBranches P)
      (exceptionalForestTarget exceptionalDegree eta n) slack) := by
  exact exists_selectedF0_for_exceptionalDegree P
    (nontrivialMajorBranches P) exceptionalDegree eta n slack hslack
    (fun j _ ↦ hsmall j) hmass

end Erdos547b.ZhaoClaim615SourceFamilyTarget

#print axioms Erdos547b.ZhaoClaim615SourceFamilyTarget.exceptionalForestTarget_lower
#print axioms Erdos547b.ZhaoClaim615SourceFamilyTarget.exceptionalForestTarget_lt_add_one
#print axioms Erdos547b.ZhaoClaim615SourceFamilyTarget.exists_selectedF0_for_exceptionalDegree
#print axioms Erdos547b.ZhaoClaim615SourceFamilyTarget.exists_balancedSelectedF0_for_exceptionalDegree
#print axioms Erdos547b.ZhaoClaim615SourceFamilyTarget.exists_nontrivialSelectedF0_for_exceptionalDegree
