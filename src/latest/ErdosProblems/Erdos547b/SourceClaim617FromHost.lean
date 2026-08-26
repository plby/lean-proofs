/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim617Reinsert
import ErdosProblems.Erdos547b.SourceClaim617Paths

/-! # Actual-host Claim 6.17: the S1 crossing is sparse -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClaim617FromHost

open Finset SimpleGraph Erdos547b.TreePartition Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceClaim617Switch
open Erdos547b.ZhaoSourceClaim617CleanCount Erdos547b.ZhaoSourceClaim617Reinsert
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U} (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (O : Output W Q S (branchMass P (sideBranches P 1)))

include hT in
theorem sourceS1_crossing_lt
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G) :
    (((padGraph (reduced W)).interedges O.D.S1 O.D.V2).card : ℝ) <
      16 * (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 := by
  by_contra hfail
  have hdense := le_of_not_gt hfail
  obtain ⟨sw⟩ := exists_switch W Q S O hα hα1 hhost horder hdense
  have hsub : (padGraph (reduced W)).interedges O.D.S1 O.D.V2 ⊆
      (padGraph (reduced W)).interedges O.D.V1 O.D.V2 := by
    intro e he
    rw [SimpleGraph.mem_interedges_iff] at he ⊢
    exact ⟨sourceS1_subset_support O.D.Min (padFinset (large W)) he.1, he.2⟩
  have hcardSub : (((padGraph (reduced W)).interedges O.D.S1 O.D.V2).card : ℝ) ≤
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hr : (0 : ℝ) < rho α := by exact_mod_cast (parameter_pos hα).2.1
  have hk : (0 : ℝ) < paddedHalf (Index W) := by
    have hs := scale_lower W Q S O hα hα1 hhost horder
    have hprod : 0 < (rho α : ℝ) * paddedHalf (Index W) := by linarith only [hs]
    exact pos_of_mul_pos_right hprod hr.le
  have hpos : 0 < (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 := mul_pos hr (sq_pos_of_pos hk)
  have hcross : (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card := by
    nlinarith only [hpos, hdense, hcardSub]
  have hp := postponedCount_le_cleanBranches W Q S hT P O hα hα1 hhost horder hcard hnot hcross
  obtain ⟨f⟩ := exists_copy_of_postponed_switch W Q S hT P hp O sw hα hα1 hhost horder hcard hnot
  exact hnot f.isContained

end Erdos547b.ZhaoSourceClaim617FromHost

#print axioms Erdos547b.ZhaoSourceClaim617FromHost.sourceS1_crossing_lt
