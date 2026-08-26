/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePathCoreAllocation
import ErdosProblems.Erdos547b.SourcePathCoreSideMass
import ErdosProblems.Erdos547b.SourceSwitchUnion

/-! # Actual union-matching allocations for the small-minor postponed core -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePathCoreSmallAllocation

open Finset SimpleGraph Erdos547b.TreePartition Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceClaim617PathNumerics Erdos547b.ZhaoSourcePathCoreMass
open Erdos547b.ZhaoSourcePathCoreNumerics Erdos547b.ZhaoClaim617CleanLoss
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceClaim617Switch
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoSourceSwitchRows
open Erdos547b.ZhaoSourceMatchingCapacityMargins Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoMatchingEdgeInclusion Erdos547b.ZhaoSourceMatchingInclusion
open Erdos547b.ZhaoSourceSwitchUnion Erdos547b.ZhaoSourcePathCoreSideMass

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U} (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (hp : postponedCount α q ≤ (cleanBranches P).card)
variable (O : Output W Q S (branchMass P (sideBranches P 1))) (sw : Switch W Q S O)

include hT in
theorem major_core_row_surplus
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1) :
    coreMass P hp 0 + 3 * (gamma α : ℝ) * q < matchingRow W Q S 0 sw.switched := by
  have hA := switched_rowA_lower W Q S O sw hα hα1 hhost horder
  have hη : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  have hηq := mul_nonneg hη (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hrow : (1 - 9 * (eta α : ℝ)) * q -
      5 * (rho α : ℝ) * paddedHalf (Index W) * W.clusterSize < matchingRow W Q S 0 sw.switched := by
    nlinarith only [hA, hηq]
  have hsurplus := core_row_surplus W P hp hT hα hα1 hhost horder hcard _ hrow
  have hminor := coreMass_nonneg P hp 1
  have hγ : (0 : ℝ) ≤ gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1.le
  have hγq := mul_nonneg hγ (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hN : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  linarith only [hsurplus, hminor, hγq, hN]

theorem minor_core_row_budget
    (hminor : (branchMass P (sideBranches P 1) : ℝ) < (fourthRoot α : ℝ) * q) :
    coreMass P hp 1 + 3 * (gamma α : ℝ) * q ≤ matchingRow W Q S 1 O.D.Mb := by
  change _ ≤ matchingRow W Q S 1
    (edgeFinsetSubgraph Q.claim67.M (padFinset (large W)) O.D.mbEdges)
  rw [matchingRow_selected, O.reserved_eq]
  exact (add_le_add (coreMass_le_original P hp 1) le_rfl).trans (O.reserved.small_lower hminor)

include hT in
theorem exists_small_coreAllocation
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hminor : (branchMass P (sideBranches P 1) : ℝ) < (fourthRoot α : ℝ) * q) :
    ∃ E : Fin 2 → Finset (MatchingEdge (fullMatching W Q S O sw)),
      Disjoint (E 0) (E 1) ∧
      (∀ s, E s ⊆ edgesAwayFromDistinguished (fullMatching W Q S O sw) (padFinset (large W))
        (Sum.inl Q.A) (Sum.inl Q.B)) ∧
      ∀ s, coreMass P hp s + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ E s, pairWeight W Q S (fullMatching W Q S O sw) (rootCluster W Q s) e := by
  have ha : sw.switched ≤ fullMatching W Q S O sw := le_sup_left
  have hb : O.D.Mb ≤ fullMatching W Q S O sw := le_sup_right
  let Ea := liftedEdges ha (allMatchingEdges sw.switched)
  let Eb := liftedEdges hb (allMatchingEdges O.D.Mb)
  refine ⟨![Ea, Eb], ?_, ?_, ?_⟩
  · exact liftedEdges_disjoint_of_support ha hb (switched_disjoint_reserved W Q S O sw) _ _
  · intro s e _
    exact fullMatching_all_edges_away W Q S O sw (mem_allMatchingEdges _ e)
  · intro s
    fin_cases s
    · change _ ≤ ∑ e ∈ Ea, pairWeight W Q S (fullMatching W Q S O sw) (rootCluster W Q 0) e
      rw [sum_lifted_all_row W Q S ha (switched_properties W Q S O sw).1]
      exact (major_core_row_surplus W Q S hT P hp O sw hα hα1 hhost horder hcard).le
    · change _ ≤ ∑ e ∈ Eb, pairWeight W Q S (fullMatching W Q S O sw) (rootCluster W Q 1) e
      rw [sum_lifted_all_row W Q S hb O.D.Mb_isMatching]
      exact minor_core_row_budget W Q S P hp O hminor

end Erdos547b.ZhaoSourcePathCoreSmallAllocation

#print axioms Erdos547b.ZhaoSourcePathCoreSmallAllocation.major_core_row_surplus
#print axioms Erdos547b.ZhaoSourcePathCoreSmallAllocation.minor_core_row_budget
#print axioms Erdos547b.ZhaoSourcePathCoreSmallAllocation.exists_small_coreAllocation
