/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceExceptionalNumerics
import ErdosProblems.Erdos547b.SourceExceptionalRowBounds

/-!
# Source-scale finite gates for the raw-row discrepancy allocation

The total-row and normalized-row cases share these explicit estimates.
The original per-edge overshoot is retained as twice the cluster size.
-/

namespace Erdos547b.ZhaoSourceRawDiscrepancyNumerics

open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceExceptionalNumerics

theorem scalar_gates (t g q N fb : ℝ)
    (ht : 0 ≤ t) (htSmall : t ≤ 1 / 100) (hg : 0 ≤ g) (hgSmall : g ≤ t ^ 2 / 1000000)
    (hq : 0 < q) (hN : 0 ≤ N) (hNsmall : N ≤ t ^ 2 * q / 500) (hfb : fb ≤ q / 2) :
    10 * t ^ 2 < 1 ∧ 10 * t ^ 2 ≤ t ∧
      10 * t ^ 2 * q + 2 * (3 * g * q) ≤ 13 * t * q ∧
      10 * t ^ 2 * q + 2 * (3 * g * q) + 2 * N ≤ t * (13 * t) * q ∧
      fb + 3 * g * q + 2 * N < (1 - 10 * t ^ 2) * q ∧
      (2 + t - 10 * t ^ 2) * (3 * g * q) + (1 + t) * (2 * N) ≤
        (t / 2 - (10 * t ^ 2) / 2 - t * (10 * t ^ 2)) * q := by
  have ht1 : t ≤ 1 := by linarith only [htSmall]
  have h2 : t ^ 2 ≤ t / 100 := by
    nlinarith only [mul_nonneg ht (sub_nonneg.mpr htSmall)]
  have h2t : t ^ 2 ≤ t := by linarith only [h2, ht]
  have h21 : t ^ 2 ≤ 1 / 100 := by linarith only [h2, htSmall]
  have h3 : t ^ 3 ≤ t / 10000 := by
    have h := mul_le_mul_of_nonneg_right h2 ht
    nlinarith only [h, h2]
  have h2q := mul_le_mul_of_nonneg_right h2 hq.le
  have h2tq := mul_le_mul_of_nonneg_right h2t hq.le
  have h21q := mul_le_mul_of_nonneg_right h21 hq.le
  have h3q := mul_le_mul_of_nonneg_right h3 hq.le
  have hgq := mul_le_mul_of_nonneg_right hgSmall hq.le
  have htq : 0 ≤ t * q := mul_nonneg ht hq.le
  have htsq : 0 ≤ t ^ 2 * q := mul_nonneg (sq_nonneg t) hq.le
  have hbudget : 10 * t ^ 2 * q + 2 * (3 * g * q) + 2 * N ≤ t * (13 * t) * q := by
    nlinarith only [hgq, hNsmall, htsq]
  refine ⟨by linarith only [h2, htSmall], by linarith only [h2, ht], ?_, hbudget, ?_, ?_⟩
  · nlinarith only [hbudget, h2tq, hN]
  · nlinarith only [hfb, hgq, hNsmall, h21q, hq]
  · have hfactor1 : 2 + t - 10 * t ^ 2 ≤ 3 := by nlinarith only [ht1, sq_nonneg t]
    have hfactor2 : 1 + t ≤ 2 := by linarith only [ht1]
    have hleft1 := mul_le_mul_of_nonneg_right hfactor1 (show 0 ≤ 3 * g * q by positivity)
    have hleft2 := mul_le_mul_of_nonneg_right hfactor2 (show 0 ≤ 2 * N by positivity)
    have hleft : (2 + t - 10 * t ^ 2) * (3 * g * q) + (1 + t) * (2 * N) ≤ t * q / 100 := by
      nlinarith only [hleft1, hleft2, hgq, hNsmall, h2tq, htq]
    nlinarith only [hleft, h2q, h3q, htq]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

theorem actual_raw_gates (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (fb : ℝ) (hfb : fb ≤ (q : ℝ) / 2) :
    10 * (fourthRoot α : ℝ) ^ 2 < 1 ∧ 10 * (fourthRoot α : ℝ) ^ 2 ≤ (fourthRoot α : ℝ) ∧
      10 * (fourthRoot α : ℝ) ^ 2 * q + 2 * (3 * (gamma α : ℝ) * q) ≤ 13 * (fourthRoot α : ℝ) * q ∧
      10 * (fourthRoot α : ℝ) ^ 2 * q + 2 * (3 * (gamma α : ℝ) * q) + 2 * W.clusterSize ≤
        (fourthRoot α : ℝ) * (13 * (fourthRoot α : ℝ)) * q ∧
      fb + 3 * (gamma α : ℝ) * q + 2 * W.clusterSize < (1 - 10 * (fourthRoot α : ℝ) ^ 2) * q ∧
      (2 + (fourthRoot α : ℝ) - 10 * (fourthRoot α : ℝ) ^ 2) * (3 * (gamma α : ℝ) * q) +
          (1 + (fourthRoot α : ℝ)) * (2 * W.clusterSize) ≤
        ((fourthRoot α : ℝ) / 2 - (10 * (fourthRoot α : ℝ) ^ 2) / 2 -
          (fourthRoot α : ℝ) * (10 * (fourthRoot α : ℝ) ^ 2)) * q := by
  subst hostN
  have hp := parameter_pos hα
  have hu := parameter_upper_bounds hα hα1
  have he1 := (parameter_gates hα hα1).2.1
  have he3 : eta α ^ 3 ≤ 1 := pow_le_one₀ hp.2.2.1.le he1
  have htSmallQ : 100 * fourthRoot α ≤ 1 := by linarith only [hu.2.2.2.1, he3]
  have htSmallR : (100 : ℝ) * (fourthRoot α : ℝ) ≤ 1 := by exact_mod_cast htSmallQ
  have hd : degreeError α ≤ fourthRoot α ^ 2 / 100 := (reservoir_cleanup_bounds hα hα1).2.2.2.1
  have hgSmallQ : gamma α ≤ fourthRoot α ^ 2 / 1000000 := by
    linarith only [hd, hu.2.2.2.2.2.1, sq_nonneg (fourthRoot α)]
  have hgSmall : (gamma α : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 / 1000000 := by exact_mod_cast hgSmallQ
  have hN := (degreeForm_source_bounds hα hα1 W horder).2.2
  have hdR : (degreeError α : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 := by
    have h : degreeError α ≤ fourthRoot α ^ 2 := by linarith only [hd, sq_nonneg (fourthRoot α)]
    exact_mod_cast h
  have hdq := mul_le_mul_of_nonneg_right hdR (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hq : (0 : ℝ) < q := by
    have hh := W.five_ordinaryParts_le_host
    have hparts := W.ordinaryParts_pos
    have hqNat : 0 < q := by omega
    exact_mod_cast hqNat
  apply scalar_gates (fourthRoot α : ℝ) (gamma α : ℝ) q W.clusterSize fb
    (by exact_mod_cast hp.2.2.2.1.le) (by linarith only [htSmallR])
    (by exact_mod_cast hp.2.2.2.2.2.2.1.le) hgSmall hq (Nat.cast_nonneg _)
  · linarith only [hN, hdq]
  · exact hfb

end Erdos547b.ZhaoSourceRawDiscrepancyNumerics

#print axioms Erdos547b.ZhaoSourceRawDiscrepancyNumerics.scalar_gates
#print axioms Erdos547b.ZhaoSourceRawDiscrepancyNumerics.actual_raw_gates
