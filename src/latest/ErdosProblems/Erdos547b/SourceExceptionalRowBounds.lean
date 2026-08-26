/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceParentCleanup
import ErdosProblems.Erdos547b.SourceFamilyCapacity

/-!
# Actual source rows and the exceptional residual margin

All row lower bounds and per-edge caps come from the same cleaned source
roots. The explicit parameter schedule pays the large-case residual
losses, including the whole matching-edge crossing overshoot.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceExceptionalRowBounds

open Finset SimpleGraph
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceFamilyCapacity

theorem eta_appendix_valid (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    FamilyKind.Valid α (.appendix (eta α : ℝ)) := by
  have hpos := parameter_pos hα
  have hupper := parameter_upper_bounds hα hα1
  have hr1 : rho α ≤ 1 := hupper.2.1.trans hupper.1
  have he1 : eta α ≤ 1 := by linarith only [hupper.2.2.1, hr1]
  have he3 : eta α ^ 3 ≤ eta α := pow_succ_le_self hpos.2.2.1.le he1 2
  have hcut : densityCutoff α ≤ eta α := by
    unfold densityCutoff
    linarith only [hupper.2.2.2.2.1, hupper.2.2.2.1, he3, hpos.2.2.1]
  have hehalf : eta α ≤ 1 / 2 := by linarith only [hupper.2.2.1, hr1]
  have he2 : 2 * eta α ≤ 1 := by linarith only [hehalf]
  have he2R : (2 : ℝ) * (eta α : ℝ) ≤ 1 := by exact_mod_cast he2
  exact ⟨by exact_mod_cast hcut, by linarith only [he2R]⟩

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

abbrev awayEdges := edgesAwayFromDistinguished Q.claim67.M
  (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)

abbrev sideWeight (s : Fin 2) := rowWeight W S (Sum.inl (rootCluster W Q s))

theorem sideWeight_nonneg (s : Fin 2) (e : MatchingEdge Q.claim67.M) :
    0 ≤ sideWeight W Q S s e := by
  have h := CleanSourceWitness.source_rows W S
  fin_cases s
  · exact h.weightA_nonneg e
  · exact h.weightB_nonneg e

theorem sideWeight_le (s : Fin 2) (e : MatchingEdge Q.claim67.M) :
    sideWeight W Q S s e ≤ 2 * W.clusterSize := by
  have h := CleanSourceWitness.source_rows W S
  fin_cases s
  · exact h.weightA_le e
  · exact h.weightB_le e

theorem awayWeight_lower (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) (s : Fin 2) :
    (1 - 10 * (fourthRoot α : ℝ) ^ 2) * q ≤ ∑ e ∈ awayEdges W Q, sideWeight W Q S s e := by
  have h := CleanSourceWitness.away_degrees W hα hα1 S hhost horder
  fin_cases s
  · exact h.1
  · exact h.2

theorem large_residual_margin (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    10 * (fourthRoot α : ℝ) ^ 2 * q + 2 * (3 * (gamma α : ℝ) * q) +
      2 * W.clusterSize + 15 * (fourthRoot α : ℝ) * q ≤ (eta α : ℝ) ^ 3 * q := by
  subst hostN
  have hN := (degreeForm_source_bounds hα hα1 W horder).2.2
  have hs : 15 * (fourthRoot α : ℝ) + 10 * (fourthRoot α : ℝ) ^ 2 +
      6 * (gamma α : ℝ) ≤ (eta α : ℝ) ^ 3 / 1000 := by
    exact_mod_cast (exceptional_saving_margin hα hα1).le
  have hupper := parameter_upper_bounds hα hα1
  have hdt : (degreeError α : ℝ) ≤ fourthRoot α := by exact_mod_cast hupper.2.2.2.2.1
  have hte : (fourthRoot α : ℝ) ≤ (eta α : ℝ) ^ 3 / 1000000 := by
    exact_mod_cast hupper.2.2.2.1
  have hsQ := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hdQ := mul_le_mul_of_nonneg_right (hdt.trans hte) (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have heta : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  have hnonneg : 0 ≤ (eta α : ℝ) ^ 3 * q := by positivity
  nlinarith only [hN, hsQ, hdQ, hnonneg]

theorem small_residual_margin (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    10 * (fourthRoot α : ℝ) ^ 2 * q + 4 * (fourthRoot α : ℝ) * q +
      3 * (gamma α : ℝ) * q ≤ (eta α : ℝ) ^ 3 * q := by
  have hpos := parameter_pos hα
  have ht : (0 : ℝ) ≤ fourthRoot α := by exact_mod_cast hpos.2.2.2.1.le
  have hg : (0 : ℝ) ≤ gamma α := by exact_mod_cast hpos.2.2.2.2.2.2.1.le
  have heta : (0 : ℝ) ≤ eta α := by exact_mod_cast hpos.2.2.1.le
  have hs : 15 * (fourthRoot α : ℝ) + 10 * (fourthRoot α : ℝ) ^ 2 +
      6 * (gamma α : ℝ) ≤ (eta α : ℝ) ^ 3 / 1000 := by
    exact_mod_cast (exceptional_saving_margin hα hα1).le
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hsQ := mul_le_mul_of_nonneg_right hs hq
  nlinarith only [hsQ, mul_nonneg ht hq, mul_nonneg hg hq,
    mul_nonneg (pow_nonneg heta 3) hq]

end Erdos547b.ZhaoSourceExceptionalRowBounds

#print axioms Erdos547b.ZhaoSourceExceptionalRowBounds.awayWeight_lower
#print axioms Erdos547b.ZhaoSourceExceptionalRowBounds.large_residual_margin
#print axioms Erdos547b.ZhaoSourceExceptionalRowBounds.eta_appendix_valid
#print axioms Erdos547b.ZhaoSourceExceptionalRowBounds.small_residual_margin
