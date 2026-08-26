/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceNearFullFromHost
import ErdosProblems.Erdos547b.SourceClaim61Entry

/-!
# Complete entry from the source host to the near-full matching

No regularity witness, rich certificate, clean roots, tree partition,
exceptional-family bound or reserved matching is assumed here.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceNearFullEntry

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceNearFullFromHost Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceClaim61Entry Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoStability Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoClaim617BranchCount

theorem exists_source_nearFullMatching
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) {n : ℕ}
    (H : SimpleGraph (Fin (2 * n - 2))) [DecidableRel H.Adj]
    (hn : sourceRamseyThreshold α ≤ n)
    (hlarge : n - 1 ≤ (highDegreeVertices H (n - 1)).card)
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (T : SimpleGraph (Fin n)) [DecidableRel T.Adj] (hT : T.IsTree)
    (hnot : ¬T.IsContained H) :
    ∃ (W : Witness α (n - 1) (degreeFormBound (epsilon α) (requestedClusters α)) H)
      (Q : Certificate W) (S : CleanSourceWitness W Q) (root : Fin n)
      (P : ZhaoForestPartition T root (freshBranchBound α W.clusterSize)),
      (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize ∧
      (∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize) ∧
      ∃ O : Output W Q S (branchMass P (sideBranches P 1)),
        (fourthRoot α : ℝ) * (n - 1 : ℕ) ≤ (branchMass P (sideBranches P 1) : ℝ) →
          (1 - 9 * (eta α : ℝ)) * (n - 1 : ℕ) < ∑ e ∈ O.D.minEdges, sideWeight W Q S 1 e := by
  have hn2 : 2 ≤ n := by unfold sourceRamseyThreshold orderThreshold at hn; omega
  have horder : orderThreshold α (degreeFormBound (epsilon α) (requestedClusters α)) ≤ n - 1 := by
    unfold sourceRamseyThreshold at hn
    omega
  have hhost : 2 * n - 2 = 2 * (n - 1) := by omega
  obtain ⟨W, hW⟩ := exists_source_claim61 hα hα1 H hn hlarge
  obtain ⟨Q⟩ := hW.resolve_left hnotEC1
  obtain ⟨S⟩ := exists_clean_source W hα hα1 Q hhost horder
  let root : Fin n := ⟨0, by omega⟩
  obtain ⟨P, hroots, hsmall, O, hB⟩ := exists_partition_and_output_of_notEC1 hT H W Q S
    hα hα1 horder hlarge hnotEC1 (Fintype.card_fin n) hnot root
  exact ⟨W, Q, S, root, P, hroots, hsmall, O, hB⟩

end Erdos547b.ZhaoSourceNearFullEntry

#print axioms Erdos547b.ZhaoSourceNearFullEntry.exists_source_nearFullMatching
