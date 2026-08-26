/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim617Switch
import ErdosProblems.Erdos547b.SourceExceptionalRowBounds

/-!
# Actual source-row capacity after switching

The new row degree is a sum on the new support, not a new Claim-6.7
certificate. Exact endpoint sums identify the old row and charge only the
freed partner set.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSwitchRows

open Finset SimpleGraph Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceNearFullFromHost Erdos547b.ZhaoSourceCrossingClusters
open Erdos547b.ZhaoSourceClaim617Switch Erdos547b.ZhaoClaim617SwitchNumerics
open Erdos547b.ZhaoMatchingSupportSeparation Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceExceptionalRowBounds Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.TreePartition Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFreshPartitionBounds Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim616HierarchyClassification

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

def vertexWeight (s : Fin 2) (x : EvenPadding (Index W)) : ℝ :=
  W.clusterSize * rootDensity W S (Sum.inl (rootCluster W Q s)) x

def matchingRow (s : Fin 2) (N : (padGraph (reduced W)).Subgraph) : ℝ :=
  ∑ x ∈ matchingSupport N, vertexWeight W Q S s x

theorem vertexWeight_nonneg (s : Fin 2) (x : EvenPadding (Index W)) :
    0 ≤ vertexWeight W Q S s x := by
  unfold vertexWeight rootDensity twoRootSourceDensity rootedSourceDensity
  split_ifs <;> positivity

theorem vertexWeight_le (s : Fin 2) (x : EvenPadding (Index W)) :
    vertexWeight W Q S s x ≤ W.clusterSize := by
  have hC : rootCluster W Q s = Q.A ∨ rootCluster W Q s = Q.B := by
    unfold rootCluster
    split_ifs <;> simp
  have h := source_entry_le_one W Q S (rootCluster W Q s) hC x
  exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg W.clusterSize)).trans_eq (mul_one _)

theorem matchingRow_selected (s : Fin 2) (E : Finset (MatchingEdge Q.claim67.M)) :
    matchingRow W Q S s (edgeFinsetSubgraph Q.claim67.M (padFinset (large W)) E) =
      ∑ e ∈ E, sideWeight W Q S s e := by
  rw [matchingRow, sum_selectedSupport Q.claim67.M Q.claim67.isMatching]
  apply Finset.sum_congr rfl
  intro e _
  change (W.clusterSize : ℝ) * _ + W.clusterSize * _ = W.clusterSize * (_ + _)
  ring

variable {fb : ℝ} (O : Output W Q S fb) (D : Switch W Q S O)

theorem switched_row_loss (s : Fin 2) :
    (∑ e ∈ O.D.minEdges, sideWeight W Q S s e) ≤ matchingRow W Q S s D.switched +
      (switchCount (rho α : ℝ) (paddedHalf (Index W)) : ℝ) * W.clusterSize := by
  have h := D.weight_loss O.D.Min_isMatching (targets_disjoint_original W Q S O)
    (vertexWeight W Q S s) W.clusterSize (vertexWeight_nonneg W Q S s)
    (fun x _ => vertexWeight_le W Q S s x)
  change matchingRow W Q S s O.D.Min ≤ matchingRow W Q S s D.switched + _ at h
  exact (matchingRow_selected W Q S s O.D.minEdges).symm.le.trans h

theorem switched_row_loss_le_scale (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) (s : Fin 2) :
    (∑ e ∈ O.D.minEdges, sideWeight W Q S s e) ≤ matchingRow W Q S s D.switched +
      5 * (rho α : ℝ) * paddedHalf (Index W) * W.clusterSize := by
  have h := (switchCount_bounds (scale_lower W Q S O hα hα1 hhost horder)).2
  exact (switched_row_loss W Q S O D s).trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg W.clusterSize)))

theorem switched_rowA_lower (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    (1 - 8 * (eta α : ℝ)) * q -
      5 * (rho α : ℝ) * paddedHalf (Index W) * W.clusterSize < matchingRow W Q S 0 D.switched := by
  have hA := O.degreeA_order W Q S hα hα1
  have h := switched_row_loss_le_scale W Q S O D hα hα1 hhost horder 0
  linarith only [hA, h]

theorem switched_rowB_lower
    {U : Type*} [Fintype U] [DecidableEq U]
    {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree) {globalRoot : U}
    (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
    (sourceO : Output W Q S (branchMass P (sideBranches P 1))) (sw : Switch W Q S sourceO)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G)
    (hminor : (fourthRoot α : ℝ) * q ≤ (branchMass P (sideBranches P 1) : ℝ)) :
    (1 - 9 * (eta α : ℝ)) * q -
      5 * (rho α : ℝ) * paddedHalf (Index W) * W.clusterSize < matchingRow W Q S 1 sw.switched := by
  have hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
    subst hostN
    exact freshPartition_root_bound hα hα1 W horder hcard P
  have hnotHost : ¬Nonempty (T.Copy (embeddingHost W)) := by
    rintro ⟨f⟩
    exact hnot (((SimpleGraph.Copy.ofLE (embeddingHost W) G
      (embeddingHost_le_original W)).comp f).isContained)
  have hB := degreeB_order_of_largeMinor W Q S hT P sourceO hα hα1 hhost horder hcard
    (canonical_branch_size_le_small P) hroots hnotHost hminor
  have h := switched_row_loss_le_scale W Q S sourceO sw hα hα1 hhost horder 1
  linarith only [hB, h]

end Erdos547b.ZhaoSourceSwitchRows

#print axioms Erdos547b.ZhaoSourceSwitchRows.matchingRow_selected
#print axioms Erdos547b.ZhaoSourceSwitchRows.switched_row_loss
#print axioms Erdos547b.ZhaoSourceSwitchRows.switched_rowA_lower
#print axioms Erdos547b.ZhaoSourceSwitchRows.switched_rowB_lower
