/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim610BalancedMass
import ErdosProblems.Erdos547b.Claim610HostEmbedding

/-!
# Zhao Claim 6.10

This module combines the non-EC1 host argument with the source leaf count and
constructs the balanced branch selection consumed by the unbalanced case of
Claim 6.15.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim610Full

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim610BalancedMass
open Erdos547b.ZhaoClaim610HostEmbedding

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Claim 6.10 in its direct mass form.  The final displayed hypothesis is
the explicit scalar comparison between the admissible dense-core order and
the leaf threshold required by the branch count. -/
theorem balancedMajorBranchMass_ge_of_not_extremalCaseOne
    {n k : ℕ} (hn : 2 ≤ n) (beta : ℚ)
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (hlarge : n - 1 ≤
      #(Finset.univ.filter fun v ↦ n - 1 ≤ G.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne beta G)
    (hnumeric : (2 * k * ((n - 1 : ℕ) : ℚ)) ≤
      beta * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ))
    (hT : T.IsTree) (hcard : 3 ≤ Fintype.card V)
    (horder : Fintype.card V - 1 ≤ n - 1)
    (hnotContained : ¬T.IsContained G)
    (P : ZhaoForestPartition T globalRoot small)
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (target : ℕ)
    (hthreshold : ((Fintype.card V - (k + 1) : ℕ) : ℝ) ≤
      (1 - 2 * alpha) *
          ((branchMass P (halfBranches P) : ℝ) - target) -
        2 * P.numParts) :
    target ≤ branchMass P (balancedMajorBranches P alpha) := by
  have hleafNat := card_graphLeaves_lt_sub_of_not_isContained hn beta G hlarge
    hnotEC1 hnumeric T hT hcard horder hnotContained
  have hleafReal : (#(graphLeaves T) : ℝ) <
      (Fintype.card V - (k + 1) : ℕ) := by
    exact_mod_cast hleafNat
  exact balancedMajorBranchMass_ge_of_leaf_upper P alpha halpha0 halphaHalf
    target (hleafReal.trans_le hthreshold)

/-- Claim 6.10 with the finite balanced source forest selected internally. -/
theorem exists_balancedSelectedF0_of_not_extremalCaseOne
    {n k : ℕ} (hn : 2 ≤ n) (beta : ℚ)
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (hlarge : n - 1 ≤
      #(Finset.univ.filter fun v ↦ n - 1 ≤ G.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne beta G)
    (hnumeric : (2 * k * ((n - 1 : ℕ) : ℚ)) ≤
      beta * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ))
    (hT : T.IsTree) (hcard : 3 ≤ Fintype.card V)
    (horder : Fintype.card V - 1 ≤ n - 1)
    (hnotContained : ¬T.IsContained G)
    (P : ZhaoForestPartition T globalRoot small)
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (target slack : ℕ) (hslack : 0 < slack)
    (hbranchSmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hthreshold : ((Fintype.card V - (k + 1) : ℕ) : ℝ) ≤
      (1 - 2 * alpha) *
          ((branchMass P (halfBranches P) : ℝ) - target) -
        2 * P.numParts) :
    Nonempty (SelectedF0 P (balancedMajorBranches P alpha) target slack) := by
  apply exists_balancedSelectedF0 P alpha target slack hslack hbranchSmall
  exact balancedMajorBranchMass_ge_of_not_extremalCaseOne hn beta G hlarge
    hnotEC1 hnumeric hT hcard horder hnotContained P alpha halpha0 halphaHalf
    target hthreshold

end Erdos547b.ZhaoClaim610Full

#print axioms Erdos547b.ZhaoClaim610Full.balancedMajorBranchMass_ge_of_not_extremalCaseOne
#print axioms Erdos547b.ZhaoClaim610Full.exists_balancedSelectedF0_of_not_extremalCaseOne
