/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim610BranchForestLeaves

/-!
# The balanced-mass conclusion of Zhao Claim 6.10

This file isolates the exact source contrapositive.  Once a separate host
argument gives the displayed upper bound on the original leaves, the
balanced branches in the canonical major parity half have the required mass.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim610BalancedMass

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim610BranchForestLeaves

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The complement of the balanced branch family inside the selected
component-parity half. -/
def unbalancedMajorBranches
    (P : ZhaoForestPartition T globalRoot small) (alpha : ℝ) :
    Finset (BranchIndex P) :=
  halfBranches P \ balancedMajorBranches P alpha

@[simp] theorem mem_unbalancedMajorBranches
    (P : ZhaoForestPartition T globalRoot small) (alpha : ℝ)
    (j : BranchIndex P) :
    j ∈ unbalancedMajorBranches P alpha ↔
      j ∈ halfBranches P ∧
        ¬(alpha < branchRatio P j ∧ branchRatio P j < 1 - alpha) := by
  rw [unbalancedMajorBranches, Finset.mem_sdiff]
  constructor
  · intro hj
    refine ⟨hj.1, ?_⟩
    intro hratio
    exact hj.2 ((mem_balancedMajorBranches P alpha j).2 ⟨hj.1, hratio⟩)
  · rintro ⟨hjhalf, hjratio⟩
    refine ⟨hjhalf, ?_⟩
    intro hjbal
    exact hjratio ((mem_balancedMajorBranches P alpha j).1 hjbal).2

theorem balanced_union_unbalancedMajorBranches
    (P : ZhaoForestPartition T globalRoot small) (alpha : ℝ) :
    balancedMajorBranches P alpha ∪ unbalancedMajorBranches P alpha =
      halfBranches P := by
  rw [unbalancedMajorBranches]
  exact Finset.union_sdiff_of_subset (by
    intro j hj
    exact (mem_balancedMajorBranches P alpha j).1 hj |>.1)

theorem balanced_disjoint_unbalancedMajorBranches
    (P : ZhaoForestPartition T globalRoot small) (alpha : ℝ) :
    Disjoint (balancedMajorBranches P alpha)
      (unbalancedMajorBranches P alpha) := by
  rw [unbalancedMajorBranches, Finset.disjoint_left]
  intro j hjbal hjdiff
  exact (Finset.mem_sdiff.mp hjdiff).2 hjbal

/-- Exact mass decomposition of the canonical major parity half. -/
theorem branchMass_balanced_add_unbalanced
    (P : ZhaoForestPartition T globalRoot small) (alpha : ℝ) :
    branchMass P (balancedMajorBranches P alpha) +
        branchMass P (unbalancedMajorBranches P alpha) =
      branchMass P (halfBranches P) := by
  rw [branchMass, branchMass, branchMass,
    ← Finset.sum_union (balanced_disjoint_unbalancedMajorBranches P alpha),
    balanced_union_unbalancedMajorBranches]

/-- The unbalanced portion alone forces the corresponding original-leaf
lower bound. -/
theorem factor_mul_unbalancedMass_sub_cutLoss_le_originalLeaves
    (P : ZhaoForestPartition T globalRoot small)
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2) :
    (1 - 2 * alpha) * branchMass P (unbalancedMajorBranches P alpha) -
        2 * P.numParts ≤
      #(graphLeaves T) := by
  apply factor_mul_branchMass_sub_cutLoss_le_originalLeaves P
    (unbalancedMajorBranches P alpha) alpha halpha0 halphaHalf
  intro j hj
  exact (mem_unbalancedMajorBranches P alpha j).1 hj |>.2

/-- Claim 6.10 as the exact source contrapositive used by Lemma 6.15. -/
theorem balancedMajorBranchMass_ge_of_leaf_upper
    (P : ZhaoForestPartition T globalRoot small)
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (target : ℕ)
    (hleaf : (#(graphLeaves T) : ℝ) <
      (1 - 2 * alpha) *
          ((branchMass P (halfBranches P) : ℝ) - target) -
        2 * P.numParts) :
    target ≤ branchMass P (balancedMajorBranches P alpha) := by
  by_contra htarget
  have hbalanced :
      branchMass P (balancedMajorBranches P alpha) < target :=
    Nat.lt_of_not_ge htarget
  have hbalancedR :
      (branchMass P (balancedMajorBranches P alpha) : ℝ) < target := by
    exact_mod_cast hbalanced
  have hmass := branchMass_balanced_add_unbalanced P alpha
  have hmassR :
      (branchMass P (balancedMajorBranches P alpha) : ℝ) +
          branchMass P (unbalancedMajorBranches P alpha) =
        branchMass P (halfBranches P) := by
    exact_mod_cast hmass
  have hfactor : 0 ≤ 1 - 2 * alpha := by linarith
  have hlower := factor_mul_unbalancedMass_sub_cutLoss_le_originalLeaves P
    alpha halpha0 halphaHalf
  nlinarith

end Erdos547b.ZhaoClaim610BalancedMass

#print axioms Erdos547b.ZhaoClaim610BalancedMass.balancedMajorBranchMass_ge_of_leaf_upper
