/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedResidualNumerics
import ErdosProblems.Erdos547b.SourceMarkedResidualSource
import ErdosProblems.Erdos547b.ExceptionalResidualAllocation

/-!
# Actual residual matching allocations in both Claim 6.16 cases

The small case keeps the literal reserved matching. The large case splits
Min minus Mzero at its first A-weight threshold and uses the raw-row bound.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedResidualAllocation

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceMarkedResidualNumerics Erdos547b.ZhaoSourceMarkedResidualSource
open Erdos547b.ZhaoExceptionalResidualAllocation Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceClaim616Selection Erdos547b.ZhaoSourceCrossingClusters
open Erdos547b.ZhaoSourceExceptionalRowBounds Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb) (C : Finset (EvenPadding (Index W)))
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] {globalRoot : U} {small : ℕ}
variable (sourceP : ZhaoForestPartition T globalRoot small)
variable (F : SelectedF0Within (branchForest sourceP) (halfBranches sourceP)
  (selectionTarget W Q S O C) (freshBranchBound α W.clusterSize))

theorem exists_residualAllocation
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hfb : fb = (branchMass sourceP (sideBranches sourceP 1) : ℝ))
    (hrows : ¬fb < (fourthRoot α : ℝ) * q → ∀ R ⊆ O.D.minEdges,
      (∑ e ∈ R, sideWeight W Q S 0 e) - (∑ e ∈ R, sideWeight W Q S 1 e) ≤
        15 * (fourthRoot α : ℝ) * q) :
    ∃ E : Fin 2 → Finset (MatchingEdge Q.claim67.M),
      Disjoint (E 0) (E 1) ∧ (∀ s, E s ⊆ awayEdges W Q) ∧
      (∀ s e, e ∈ E s →
        e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges) ∧
      ∀ s, (branchMass sourceP (sideBranches sourceP s \ F.selected) : ℝ) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ E s, sideWeight W Q S s e := by
  have hM0 := MatchingDecomposition.MzeroEdges_subset_minEdges O.D C
  have hsave := selected_saving W Q S O C sourceP F
  have hforest := residual_mass_le W Q S O C sourceP F hcard
  have htotal := O.degreeA_order W Q S hα hα1
  have hmargin := residual_saving_margin W Q S O hα hα1 hhost horder
  have hγ : (0 : ℝ) ≤ gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1.le
  have ht : (0 : ℝ) ≤ fourthRoot α := by exact_mod_cast (parameter_pos hα).2.2.2.1.le
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  by_cases hsmall : fb < (fourthRoot α : ℝ) * q
  · let E1 := O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C
    have ha : (branchMass sourceP (sideBranches sourceP 0 \ F.selected) : ℝ) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ E1, sideWeight W Q S 0 e := by
      have hsum := Finset.sum_sdiff hM0 (f := sideWeight W Q S 0)
      have hγq : 0 ≤ (gamma α : ℝ) * q := by positivity
      have htq : 0 ≤ (fourthRoot α : ℝ) * q := by positivity
      have hminor : (0 : ℝ) ≤ branchMass sourceP (sideBranches sourceP 1 \ F.selected) := Nat.cast_nonneg _
      change _ ≤ ∑ e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C, sideWeight W Q S 0 e
      nlinarith only [hsum, hsave, hforest, htotal, hmargin, hγq, htq, hN, hminor]
    have hb : (branchMass sourceP (sideBranches sourceP 1 \ F.selected) : ℝ) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ O.D.mbEdges, sideWeight W Q S 1 e := by
      rw [minorResidual_eq W Q S O C sourceP F, O.reserved_eq, ← hfb]
      exact O.reserved.small_lower hsmall
    refine ⟨![E1, O.D.mbEdges], ?_, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro e he1 heb
      exact (Finset.mem_sdiff.mp (O.D.mb_subset heb)).2 (Finset.mem_sdiff.mp he1).1
    · intro s
      fin_cases s
      · exact Finset.sdiff_subset.trans (O.min_subset_away W Q S)
      · change O.D.mbEdges ⊆ awayEdges W Q
        rw [O.reserved_eq]
        exact O.reserved.subset_away
    · intro s e he
      fin_cases s
      · exact Or.inl he
      · exact Or.inr he
    · intro s
      fin_cases s
      · exact ha
      · exact hb
  · obtain ⟨Ea, Eb, hEa, hEb, hdis, _, ha, hb⟩ :=
      exists_large_residual_allocation O.D.minEdges (MatchingDecomposition.MzeroEdges O.D C)
        (sideWeight W Q S 0) (sideWeight W Q S 1) q (8 * (eta α : ℝ))
        ((crossingScale W : ℝ) * W.clusterSize / 2) (branchMass sourceP F.selected)
        (branchMass sourceP (sideBranches sourceP 0 \ F.selected))
        (branchMass sourceP (sideBranches sourceP 1 \ F.selected))
        (3 * (gamma α : ℝ) * q) (2 * W.clusterSize) (15 * (fourthRoot α : ℝ) * q)
        hM0 (by positivity) (fun e _ => sideWeight_le W Q S 0 e)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity) (by positivity)
        htotal.le hforest hsave hmargin (hrows hsmall)
    refine ⟨![Ea, Eb], hdis, ?_, ?_, ?_⟩
    · intro s
      fin_cases s
      · exact hEa.trans (Finset.sdiff_subset.trans (O.min_subset_away W Q S))
      · exact hEb.trans (Finset.sdiff_subset.trans (O.min_subset_away W Q S))
    · intro s e he
      fin_cases s
      · exact Or.inl (hEa he)
      · exact Or.inl (hEb he)
    · intro s
      fin_cases s
      · exact ha
      · exact hb.le

end Erdos547b.ZhaoSourceMarkedResidualAllocation

#print axioms Erdos547b.ZhaoSourceMarkedResidualAllocation.exists_residualAllocation
