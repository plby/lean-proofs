import ErdosProblems.Erdos1038.CircleAbelArcIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Integrals on centered arcs and their real representatives

This file converts Haar integrals over an origin-centered arc of
`AddCircle (2π)` to interval integrals over its canonical representative
`[-Q,Q]`.
-/

set_option warningAsError false

open Metric Set MeasureTheory

namespace Erdos1038

noncomputable section

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private lemma intervalIntegral_indicator_Icc_of_nested
    {f : ℝ → ℝ} {a c d b : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    (∫ x : ℝ in a..b, (Icc c d).indicator f x) =
      ∫ x : ℝ in c..d, f x := by
  have hab : a ≤ b := hac.trans (hcd.trans hdb)
  rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hcd]
  have hμab : (volume : Measure ℝ).restrict (Ioc a b) =
      volume.restrict (Icc a b) :=
    Measure.restrict_congr_set
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
  have hμcd : (volume : Measure ℝ).restrict (Ioc c d) =
      volume.restrict (Icc c d) :=
    Measure.restrict_congr_set
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
  rw [hμab, hμcd]
  rw [integral_indicator measurableSet_Icc]
  rw [Measure.restrict_restrict measurableSet_Icc]
  have hsubset : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  rw [inter_eq_left.mpr hsubset]

private lemma addCircle_dist_coe_zero_eq_abs
    {theta : ℝ} (htheta : theta ∈ Icc (-Real.pi) Real.pi) :
    dist (theta : AngleCircle) 0 = |theta| := by
  rw [dist_eq_norm, sub_zero]
  exact (AddCircle.norm_coe_eq_abs_iff
    (2 * Real.pi) (by positivity)).2 (by
      rw [abs_of_pos Real.two_pi_pos]
      rw [show 2 * Real.pi / 2 = Real.pi by ring, abs_le]
      exact htheta)

private lemma coe_mem_centeredClosedBall_iff
    {Q theta : ℝ} (htheta : theta ∈ Icc (-Real.pi) Real.pi) :
    (theta : AngleCircle) ∈ closedBall (0 : AngleCircle) Q ↔
      theta ∈ Icc (-Q) Q := by
  rw [mem_closedBall, addCircle_dist_coe_zero_eq_abs htheta, abs_le]
  rfl

/-- Haar integration over a centered arc is exactly integration over its
canonical real representative. -/
theorem integral_centeredClosedBall_eq_interval
    {Q : ℝ} (hQ0 : 0 ≤ Q) (hQpi : Q ≤ Real.pi)
    (F : AngleCircle → ℝ) :
    (∫ z in closedBall (0 : AngleCircle) Q, F z) =
      ∫ theta : ℝ in -Q..Q, F (theta : AngleCircle) := by
  rw [← integral_indicator measurableSet_closedBall]
  rw [← AddCircle.intervalIntegral_preimage
    (2 * Real.pi) (-Real.pi)
      ((closedBall (0 : AngleCircle) Q).indicator F)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  calc
    (∫ theta : ℝ in -Real.pi..Real.pi,
        (closedBall (0 : AngleCircle) Q).indicator F
          (theta : AngleCircle)) =
        ∫ theta : ℝ in -Real.pi..Real.pi,
          (Icc (-Q) Q).indicator
            (fun t : ℝ ↦ F (t : AngleCircle)) theta := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      rw [uIcc_of_le (by linarith [Real.pi_pos])] at htheta
      have hiff := coe_mem_centeredClosedBall_iff (Q := Q) htheta
      change (closedBall (0 : AngleCircle) Q).indicator F
          (theta : AngleCircle) =
        (Icc (-Q) Q).indicator
          (fun t : ℝ ↦ F (t : AngleCircle)) theta
      by_cases hmem : theta ∈ Icc (-Q) Q
      · rw [indicator_of_mem hmem,
          indicator_of_mem (hiff.mpr hmem)]
      · rw [indicator_of_notMem hmem,
          indicator_of_notMem ((not_congr hiff).mpr hmem)]
    _ = ∫ theta : ℝ in -Q..Q, F (theta : AngleCircle) := by
      exact intervalIntegral_indicator_Icc_of_nested
        (neg_le_neg hQpi) (by linarith) hQpi

end

end Erdos1038
