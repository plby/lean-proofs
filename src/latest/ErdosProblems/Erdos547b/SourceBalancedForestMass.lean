/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceExceptionalFamilies
import ErdosProblems.Erdos547b.Claim610BranchForestLeaves

/-!
# Global balanced branch mass and the actual parity choice

Aggregate the attached-leaf estimate over all unbalanced branches, not
only over the canonical major half. Then choose a parity carrying at
least half of the resulting balanced mass.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceBalancedForestMass

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim610BranchForestLeaves Erdos547b.ZhaoClaim68

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

def balancedBranches (ratio : ℝ) : Finset (BranchIndex P) :=
  Finset.univ.filter fun i => ratio < branchRatio P i ∧ branchRatio P i < 1 - ratio

def unbalancedBranches (ratio : ℝ) : Finset (BranchIndex P) :=
  Finset.univ \ balancedBranches P ratio

theorem mass_split (ratio : ℝ) :
    branchMass P (balancedBranches P ratio) + branchMass P (unbalancedBranches P ratio) + P.numParts =
      Fintype.card U := by
  have hs := Finset.sum_sdiff (Finset.subset_univ (balancedBranches P ratio))
    (f := (branchForest P).branches.size)
  have ht := Erdos547b.ZhaoClaim615SourceTotalMass.edgeDemand_branchForest_add_numParts P
  change branchMass P (unbalancedBranches P ratio) + branchMass P (balancedBranches P ratio) =
    branchMass P Finset.univ at hs
  change branchMass P Finset.univ + P.numParts = Fintype.card U at ht
  omega

theorem unbalanced_leaf_bound (ratio : ℝ) (hratio : 0 ≤ ratio) (hratio1 : ratio ≤ 1 / 2) :
    (1 - 2 * ratio) * (branchMass P (unbalancedBranches P ratio) : ℝ) - 2 * P.numParts ≤
      ((graphLeaves T).card : ℝ) := by
  apply factor_mul_branchMass_sub_cutLoss_le_originalLeaves P (unbalancedBranches P ratio)
    ratio hratio hratio1
  intro i hi hbalanced
  exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hbalanced⟩)

theorem balanced_mass_gt_of_leaf_bound {q : ℕ} (hcard : Fintype.card U = q + 1)
    (ratio : ℝ) (hratio : 0 ≤ ratio) (hratio1 : ratio ≤ 1 / 2)
    (hroots : 3 * (P.numParts : ℝ) ≤ ratio * q)
    (hleaves : ((graphLeaves T).card : ℝ) < (1 - 4 * ratio) * q + 1) :
    ratio * q < (branchMass P (balancedBranches P ratio) : ℝ) := by
  have hsplit : (branchMass P (balancedBranches P ratio) : ℝ) +
      (branchMass P (unbalancedBranches P ratio) : ℝ) + P.numParts = (q : ℝ) + 1 := by
    exact_mod_cast (mass_split P ratio).trans hcard
  have hsplitW := congrArg (fun x : ℝ => (1 - 2 * ratio) * x) hsplit
  have hrootOne : (1 : ℝ) ≤ P.numParts := by exact_mod_cast P.numParts_pos
  have hfactor : 0 ≤ 1 - 2 * ratio := by linarith only [hratio1]
  have hleaf := unbalanced_leaf_bound P ratio hratio hratio1
  by_contra hnot
  have hB := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) hfactor
  have hrootGain := mul_nonneg (show 0 ≤ 2 * ratio by positivity) (sub_nonneg.mpr hrootOne)
  have hnonneg : 0 ≤ ratio ^ 2 * q := by positivity
  nlinarith only [hsplitW, hleaf, hleaves, hB, hroots, hrootGain, hnonneg]

theorem balancedSide_union (ratio : ℝ) :
    balancedSideBranches P 0 ratio ∪ balancedSideBranches P 1 ratio = balancedBranches P ratio := by
  ext i
  have hside := mem_sideBranches_or_other P 0 i
  change i ∈ sideBranches P 0 ∨ i ∈ sideBranches P 1 at hside
  simp only [balancedSideBranches, balancedBranches, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  tauto

theorem balancedSide_disjoint (ratio : ℝ) :
    Disjoint (balancedSideBranches P 0 ratio) (balancedSideBranches P 1 ratio) := by
  exact (sideBranches_disjoint P 0).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem balancedSide_mass_sum (ratio : ℝ) :
    branchMass P (balancedSideBranches P 0 ratio) + branchMass P (balancedSideBranches P 1 ratio) =
      branchMass P (balancedBranches P ratio) := by
  exact (Finset.sum_union (balancedSide_disjoint P ratio)
    (f := (branchForest P).branches.size)).symm.trans
      (congrArg (fun f => branchMass P f) (balancedSide_union P ratio))

theorem exists_balancedSide_mass_gt {q : ℕ} (ratio : ℝ)
    (hmass : ratio * q < (branchMass P (balancedBranches P ratio) : ℝ)) :
    ∃ s : Fin 2, ratio * q / 2 < (branchMass P (balancedSideBranches P s ratio) : ℝ) := by
  have hsplit : (branchMass P (balancedSideBranches P 0 ratio) : ℝ) +
      (branchMass P (balancedSideBranches P 1 ratio) : ℝ) = branchMass P (balancedBranches P ratio) := by
    exact_mod_cast balancedSide_mass_sum P ratio
  by_cases h0 : ratio * q / 2 < (branchMass P (balancedSideBranches P 0 ratio) : ℝ)
  · exact ⟨0, h0⟩
  · refine ⟨1, ?_⟩
    have h0le := le_of_not_gt h0
    linarith only [hsplit, hmass, h0le]

/-- A singleton has rooted colour-zero ratio one and is not balanced. -/
theorem balancedSide_nontrivial (s : Fin 2) (ratio : ℝ) (hratio : 0 ≤ ratio)
    (i : BranchIndex P) (hi : i ∈ balancedSideBranches P s ratio) :
    2 ≤ (branchForest P).branches.size i := by
  have hpos : 0 < (branchForest P).branches.size i := by
    have h := ((branchForest P).branches.root i).isLt
    omega
  by_contra hnot
  have hsize : (branchForest P).branches.size i = 1 := by omega
  have hcolour : branchColourClass P i 0 = Finset.univ := by
    ext a
    have ha : a = (branchForest P).branches.root i := by
      apply Fin.ext
      have h1 := a.isLt
      have h2 := ((branchForest P).branches.root i).isLt
      omega
    subst a
    simp only [branchColourClass, Finset.mem_filter, Finset.mem_univ, true_and,
      Erdos547b.RegularPair.coloringTwoOfVert_root]
  have hratioOne : branchRatio P i = 1 := by
    rw [branchRatio, hcolour]
    simp only [Finset.card_univ, Fintype.card_fin, hsize, Nat.cast_one, div_one]
  have hupper := (Finset.mem_filter.mp hi).2.2
  rw [hratioOne] at hupper
  linarith only [hupper, hratio]

end Erdos547b.ZhaoSourceBalancedForestMass

#print axioms Erdos547b.ZhaoSourceBalancedForestMass.balanced_mass_gt_of_leaf_bound
#print axioms Erdos547b.ZhaoSourceBalancedForestMass.balancedSide_mass_sum
#print axioms Erdos547b.ZhaoSourceBalancedForestMass.exists_balancedSide_mass_gt
#print axioms Erdos547b.ZhaoSourceBalancedForestMass.balancedSide_nontrivial
