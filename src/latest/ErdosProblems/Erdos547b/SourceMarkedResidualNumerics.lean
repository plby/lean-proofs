/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCrossingClusters

/-!
# The literal crossing saving pays both residual matching cases

The integral scale yields saving at least rho*q/80. The near-full defect,
two source margins, first-crossing overshoot and raw discrepancy all fit.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedResidualNumerics

open Finset SimpleGraph Erdos547b.ZhaoSourceCrossingClusters
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceExceptionalCountBounds Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoEvenReducedPadding

theorem nearfull_saving_coefficient {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    8 * (eta α : ℝ) + (eta α : ℝ) ^ 3 ≤ (rho α : ℝ) / 80 := by
  have hp := parameter_pos hα
  have hu := parameter_upper_bounds hα hα1
  have hr1 : rho α ≤ 1 := hu.2.1.trans hu.1
  have he1 : eta α ≤ 1 := by linarith only [hu.2.2.1, hr1]
  have he3 : eta α ^ 3 ≤ eta α := pow_succ_le_self hp.2.2.1.le he1 2
  have h : 8 * eta α + eta α ^ 3 ≤ rho α / 80 := by
    linarith only [hu.2.2.1, he3, hp.2.1]
  exact_mod_cast h

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)

include O

theorem crossing_saving_lower (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    (rho α : ℝ) * q / 80 ≤ (crossingScale W : ℝ) * W.clusterSize / 2 := by
  have hs := (scale_bounds W Q S O hα hα1 hhost horder).2.1
  have hv := (paddedVolume_bounds W hα hα1 hhost horder).1
  have hρ : (0 : ℝ) ≤ rho α := by exact_mod_cast (parameter_pos hα).2.1.le
  have hsN := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)
  have hvρ := mul_le_mul_of_nonneg_left hv hρ
  nlinarith only [hsN, hvρ]

theorem residual_saving_margin (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    8 * (eta α : ℝ) * q + 2 * (3 * (gamma α : ℝ) * q) +
      2 * W.clusterSize + 15 * (fourthRoot α : ℝ) * q ≤
        (crossingScale W : ℝ) * W.clusterSize / 2 := by
  have hbase := large_residual_margin W hα hα1 hhost horder
  have hcoef := mul_le_mul_of_nonneg_right (nearfull_saving_coefficient hα hα1)
    (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hlower := crossing_saving_lower W Q S O hα hα1 hhost horder
  have hnonneg : 0 ≤ (fourthRoot α : ℝ) ^ 2 * q := by positivity
  nlinarith only [hbase, hcoef, hlower, hnonneg]

end Erdos547b.ZhaoSourceMarkedResidualNumerics

#print axioms Erdos547b.ZhaoSourceMarkedResidualNumerics.nearfull_saving_coefficient
#print axioms Erdos547b.ZhaoSourceMarkedResidualNumerics.crossing_saving_lower
#print axioms Erdos547b.ZhaoSourceMarkedResidualNumerics.residual_saving_margin
