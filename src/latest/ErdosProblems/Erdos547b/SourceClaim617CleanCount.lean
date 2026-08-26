/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim68Mass
import ErdosProblems.Erdos547b.SourceClaim616FromHost
import ErdosProblems.Erdos547b.Claim617CleanLoss
import ErdosProblems.Erdos547b.SourceClaim617PathNumerics

/-! The actual source host provides enough clean major-half two-paths. -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClaim617CleanCount

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFreshPartitionBounds Erdos547b.ZhaoSourceClaim68Mass
open Erdos547b.ZhaoSourceClaim616FromHost Erdos547b.ZhaoSourceClaim617PathNumerics
open Erdos547b.ZhaoClaim617CleanLoss Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim68 Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoSourceCrossingClusters
open Erdos547b.ZhaoSourceExceptionalCountBounds Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoClaim615SourceSelection

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U} (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (O : Output W Q S (branchMass P (sideBranches P 1)))

include Q S hT O in
theorem eighth_lt_cleanBranches
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G)
    (hcross : (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card) :
    (q : ℝ) / 8 < ((cleanBranches P).card : ℝ) := by
  have hm := nontrivialHalfMass_lower W Q S hT P hα hα1 hhost horder hcard hnot
  have hnotHost : ¬Nonempty (T.Copy (embeddingHost W)) := by
    rintro ⟨f⟩
    exact hnot (((SimpleGraph.Copy.ofLE (embeddingHost W) G
      (embeddingHost_le_original W)).comp f).isContained)
  have hl := largeHalfMass_lt_of_crossing W Q S hT P O hα hα1 hhost horder hcard hnotHost hcross
  have hs := (scale_bounds W Q S O hα hα1 hhost horder).2.2.1
  have hsN := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)
  have hv := (paddedVolume_bounds W hα hα1 hhost horder).2
  have hr : (0 : ℝ) ≤ rho α := by exact_mod_cast (parameter_pos hα).2.1.le
  have hvr := mul_le_mul_of_nonneg_left hv hr
  have hlarge : (largeHalfMass P : ℝ) < 3 * (rho α : ℝ) / 5 * q := by
    nlinarith only [hl, hsN, hvr]
  have hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
    subst hostN
    exact freshPartition_root_bound hα hα1 W horder hcard P
  have hc := root_count_sqrt_margin W hα hα1 hhost horder P.numParts hroots
  have hcount : nontrivialHalfMass P ≤
      2 * ((cleanBranches P).card + P.numParts) + largeHalfMass P := by
    have hclean := sizeTwoBranches_card_le_clean_add_parents P
    have hp := card_partitionParents_le_numParts P
    rw [nontrivialHalfMass_eq_two_mul_add_large]
    omega
  have hcoef : 13 * (fourthRoot α : ℝ) ^ 2 + 3 * (rho α : ℝ) / 5 ≤ 1 / 4 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (path_coefficient_bounds hα hα1).1
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_div, Rat.cast_one] at h
    exact h
  exact eighth_lt_middles hm hlarge hcount hc hcoef

include Q S hT O in
theorem postponedCount_le_cleanBranches
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G)
    (hcross : (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card) :
    postponedCount α q ≤ (cleanBranches P).card := by
  have h := (postponedCount_lt_eighth hα hα1 horder).trans
    (eighth_lt_cleanBranches W Q S hT P O hα hα1 hhost horder hcard hnot hcross)
  exact_mod_cast h.le

end Erdos547b.ZhaoSourceClaim617CleanCount

#print axioms Erdos547b.ZhaoSourceClaim617CleanCount.eighth_lt_cleanBranches
#print axioms Erdos547b.ZhaoSourceClaim617CleanCount.postponedCount_le_cleanBranches
