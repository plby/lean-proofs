/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceParameterSchedule

/-!
# Finite exceptional-selection gates

The half-threshold ceiling, one fresh branch, and absolute source margin
are all retained. The estimates use actual padded-volume bounds, not
an equality that would incorrectly count a possible dummy cluster.
-/

namespace Erdos547b.ZhaoSourceExceptionalNumerics

open Erdos547b.ZhaoSourceParameterSchedule

theorem parameter_gates {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    0 < eta α ∧ eta α ≤ 1 ∧ 8 * eta α ≤ α / 16 ∧
      epsilon α + 3 * gamma α ≤ eta α ^ 3 ∧ 1000 * degreeError α ≤ eta α := by
  have hp := parameter_pos hα
  have hu := parameter_upper_bounds hα hα1
  have hr1 : rho α ≤ 1 := hu.2.1.trans hu.1
  have he1 : eta α ≤ 1 := by linarith only [hu.2.2.1, hr1]
  have he3 : eta α ^ 3 ≤ eta α := pow_succ_le_self hp.2.2.1.le he1 2
  have hrα : rho α ≤ α / 1000 := hu.2.1
  refine ⟨hp.2.2.1, he1, ?_, ?_, ?_⟩
  · linarith only [hu.2.2.1, hrα, hα]
  · linarith only [hu.2.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.1,
      hu.2.2.2.2.2.2, pow_pos hp.2.2.1 3]
  · linarith only [hu.2.2.2.1, hu.2.2.2.2.1, he3, hp.2.2.1]

/-- Coarse scalar estimates that simultaneously imply the source-availability
and unbalanced-gain gates for the half-exceptional matching. -/
theorem half_selection_gates
    (eta ratio eps gamma q N k count m : ℝ)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hratio : 8 * eta ≤ ratio)
    (heps : 0 ≤ eps) (hgamma : 0 ≤ gamma) (hsmall : eps + 3 * gamma ≤ eta ^ 3)
    (hq : 0 ≤ q) (hN : 0 ≤ N) (hNsmall : N ≤ eta * q / 1000)
    (hvolumeLower : q / 2 ≤ k * N) (hvolumeUpper : k * N ≤ 2 * q)
    (hcountLower : eta * k / 2 ≤ count) (hcountUpper : count ≤ eta * k / 2 + 1)
    (hscale : 2 ≤ eps * N) (hm : m ≤ eps * N / 2) :
    2 * N * count + eta ^ 3 * q + 1 ≤ ratio / 2 * q ∧
      eta ^ 3 * q + 1 + m + 3 * gamma * q ≤ ratio * eta * N * count := by
  have hr0 : 0 ≤ ratio := (mul_nonneg (by norm_num) heta).trans hratio
  have heps3 : eps ≤ eta ^ 3 := by linarith only [hsmall, hgamma]
  have hsq : eta ^ 2 ≤ eta := by nlinarith only [mul_nonneg heta (sub_nonneg.mpr heta1)]
  have hcube : eta ^ 3 ≤ eta := by
    have h := mul_le_mul_of_nonneg_right hsq heta
    nlinarith only [h, hsq]
  have hepsEta : eps ≤ eta := heps3.trans hcube
  have hetaQ := mul_le_mul_of_nonneg_right heta1 hq
  have hNq : N ≤ q := by nlinarith only [hNsmall, hetaQ, hq]
  have hepsN := mul_le_mul_of_nonneg_left hNq heps
  have hepsQ := mul_le_mul_of_nonneg_right hepsEta hq
  have hcubeQ := mul_le_mul_of_nonneg_right hcube hq
  have hcountU := mul_le_mul_of_nonneg_left hcountUpper hN
  have hvolumeU := mul_le_mul_of_nonneg_left hvolumeUpper heta
  have hratioQ := mul_le_mul_of_nonneg_right hratio hq
  constructor
  · nlinarith only [hcountU, hvolumeU, hNsmall, hscale, hepsN, hepsQ, hcubeQ,
      hratioQ, mul_nonneg heta hq]
  · have hpadding := mul_le_mul_of_nonneg_right hsmall hq
    have hcountL := mul_le_mul_of_nonneg_left hcountLower hN
    have hvolumeL := mul_le_mul_of_nonneg_left hvolumeLower heta
    have hmassLower : eta * q / 4 ≤ N * count := by nlinarith only [hcountL, hvolumeL]
    have hgain := mul_le_mul_of_nonneg_left hmassLower (mul_nonneg hr0 heta)
    have hratioGain := mul_le_mul_of_nonneg_right hratio (mul_nonneg (sq_nonneg eta) hq)
    nlinarith only [hscale, hm, hepsN, hpadding, hgain, hratioGain]

end Erdos547b.ZhaoSourceExceptionalNumerics

#print axioms Erdos547b.ZhaoSourceExceptionalNumerics.parameter_gates
#print axioms Erdos547b.ZhaoSourceExceptionalNumerics.half_selection_gates
