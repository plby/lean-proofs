/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePathCoreNumerics
import ErdosProblems.Erdos547b.SourceMatchingRowIdentity
import ErdosProblems.Erdos547b.TwoRowSurplusAllocation

/-! # Actual switched allocations for the large-minor postponed core -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePathCoreAllocation

open Finset SimpleGraph Erdos547b.TreePartition Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceClaim617PathNumerics Erdos547b.ZhaoSourcePathCoreMass
open Erdos547b.ZhaoSourcePathCoreNumerics Erdos547b.ZhaoClaim617CleanLoss
open Erdos547b.ZhaoSourceNearFullFromHost Erdos547b.ZhaoSourceClaim617Switch
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoSourceSwitchRows Erdos547b.ZhaoSourceMatchingRowIdentity
open Erdos547b.ZhaoSourceMatchingCapacityMargins Erdos547b.ZhaoTwoRowSurplusAllocation
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceRootExclusions (rootCluster_cases)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U} (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (hp : postponedCount α q ≤ (cleanBranches P).card)
variable (O : Output W Q S (branchMass P (sideBranches P 1))) (sw : Switch W Q S O)

include hT in
theorem exists_large_coreAllocation
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G)
    (hminor : (fourthRoot α : ℝ) * q ≤ (branchMass P (sideBranches P 1) : ℝ)) :
    ∃ E : Fin 2 → Finset (MatchingEdge sw.switched),
      Disjoint (E 0) (E 1) ∧
      (∀ s, E s ⊆ edgesAwayFromDistinguished sw.switched (padFinset (large W))
        (Sum.inl Q.A) (Sum.inl Q.B)) ∧
      ∀ s, coreMass P hp s + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ E s, pairWeight W Q S sw.switched (rootCluster W Q s) e := by
  have hprops := switched_properties W Q S O sw
  have haway := all_edges_away W Q sw.switched (hprops.2.1.mono_right
    (show {Sum.inl Q.A, Sum.inl Q.B} ⊆ excluded W Q S O from Finset.subset_union_right))
  have hrow (s : Fin 2) : (1 - 9 * (eta α : ℝ)) * q -
      5 * (rho α : ℝ) * paddedHalf (Index W) * W.clusterSize < matchingRow W Q S s sw.switched := by
    fin_cases s
    · change _ < matchingRow W Q S 0 sw.switched
      have hA := switched_rowA_lower W Q S O sw hα hα1 hhost horder
      have hη : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
      have hηq := mul_nonneg hη (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
      nlinarith only [hA, hηq]
    · exact switched_rowB_lower W Q S hT P O sw hα hα1 hhost horder hcard hnot hminor
  have hsurplus (s : Fin 2) : coreMass P hp 0 + coreMass P hp 1 +
      2 * (3 * (gamma α : ℝ) * q) + 2 * (2 * (W.clusterSize : ℝ)) ≤
        ∑ e ∈ allMatchingEdges sw.switched, pairWeight W Q S sw.switched (rootCluster W Q s) e := by
    rw [sum_pairWeight_eq_matchingRow W Q S sw.switched hprops.1]
    exact (core_row_surplus W P hp hT hα hα1 hhost horder hcard _ (hrow s)).le
  have hγ : (0 : ℝ) ≤ gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1.le
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  obtain ⟨Ea, Eb, hEa, hEb, hdis, _, ha, hb⟩ := exists_twoRowSurplus (allMatchingEdges sw.switched)
    (pairWeight W Q S sw.switched (rootCluster W Q 0))
    (pairWeight W Q S sw.switched (rootCluster W Q 1))
    (coreMass P hp 0) (coreMass P hp 1) (3 * (gamma α : ℝ) * q) (2 * W.clusterSize)
    (fun e _ => pairWeight_nonneg W Q S sw.switched _ e)
    (fun e _ => pairWeight_nonneg W Q S sw.switched _ e)
    (fun e _ => pairWeight_le W Q S sw.switched _ (rootCluster_cases W Q 0) e)
    (fun e _ => pairWeight_le W Q S sw.switched _ (rootCluster_cases W Q 1) e)
    (coreMass_nonneg P hp 0) (coreMass_nonneg P hp 1) (by positivity) (by positivity)
    (hsurplus 0) (hsurplus 1)
  exact ⟨![Ea, Eb], hdis, (by intro s; fin_cases s; exact hEa.trans haway; exact hEb.trans haway),
    (by intro s; fin_cases s; exact ha.le; exact hb.le)⟩

end Erdos547b.ZhaoSourcePathCoreAllocation

#print axioms Erdos547b.ZhaoSourcePathCoreAllocation.exists_large_coreAllocation
