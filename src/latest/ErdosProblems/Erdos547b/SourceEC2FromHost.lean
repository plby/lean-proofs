/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceSparseCut

/-! # The omitted-tree non-EC1 host has an actual sparse cut after vertex pruning -/

open scoped SimpleGraph Classical
noncomputable section
namespace Erdos547b.ZhaoSourceEC2FromHost

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoStability Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceSparseCut
open Erdos547b.ZhaoSourceClaim618FromHost Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoClaim617BranchCount

variable {α : ℚ} {n M : ℕ}
variable (H : SimpleGraph (Fin (2 * n - 2))) [DecidableRel H.Adj]
variable (W : Witness α (n - 1) M H) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U}
variable (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (O : Output W Q S (branchMass P (sideBranches P 1)))

include Q S O hT in
theorem pruned_extremalCaseTwo_of_notEC1
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ n - 1)
    (hlarge : n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ H.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (hcard : Fintype.card U = n) (hnot : ¬T.IsContained H)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    ZhaoExtremalCaseTwo α (pruneSmallEdges H {v | n - 1 ≤ H.degree v}) := by
  have hn : 2 ≤ n := by
    have hh := W.five_ordinaryParts_le_host
    have hp := W.ordinaryParts_pos
    omega
  have hcross := sourceV1_highDensity_crossing_lt H W Q S hT P O hα hα1 horder hlarge hnotEC1
    hcard hnot hsmall hroots
  obtain ⟨A, B, hAB, hcover, hA, hB, hcardCross⟩ :=
    exists_balanced_sparse_cut W Q S O hα hα1 (by omega) horder hcross
  have hcrossQ : ((((pruneSmallEdges H {v | n - 1 ≤ H.degree v}).interedges A B).card : ℚ)) ≤
      α * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) := by
    have hR := hcardCross.le
    rw [pow_two, ← mul_assoc] at hR
    exact_mod_cast hR
  have hden := edgeDensity_le_of_card_interedges_le
    (pruneSmallEdges H {v | n - 1 ≤ H.degree v}) A B (n - 1) (by omega) hA hB α hcrossQ
  refine ⟨A, B, ⟨hAB, hcover, hA, hB⟩, ?_⟩
  convert hden using 1
  congr!

end Erdos547b.ZhaoSourceEC2FromHost

#print axioms Erdos547b.ZhaoSourceEC2FromHost.pruned_extremalCaseTwo_of_notEC1
