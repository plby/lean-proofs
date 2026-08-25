/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.Grid

/-!
# A quantitative tail bound for the angular Bessel kernel

The energy in this file is a small variant of the classical Sonin energy.  Its derivative is
nonpositive, and the rational enclosure at `3 * 157 / 50` supplied by `Grid` will give the
explicit bound used for the infinite tail of the Erdős--232 dual certificate.
-/

open Filter MeasureTheory Metric intervalIntegral
open scoped ENNReal Topology Interval

namespace Erdos232

noncomputable def besselEnergy (x : ℝ) : ℝ :=
  x / 2 * (besselDerivative 0 x ^ 2 + besselDerivative 1 x ^ 2) +
    besselDerivative 0 x * besselDerivative 1 x / 2 +
    besselDerivative 0 x ^ 2 / (4 * x)

theorem hasDerivAt_besselEnergy {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt besselEnergy (-besselDerivative 0 x ^ 2 / (4 * x ^ 2)) x := by
  have h0 := hasDerivAt_besselDerivative 0 x
  have h1 := hasDerivAt_besselDerivative 1 x
  have hid := hasDerivAt_id x
  have hden : HasDerivAt (fun y : ℝ => 4 * y) 4 x := by
    simpa only [id_eq, mul_one] using hid.const_mul (4 : ℝ)
  have hraw :=
    ((hid.div_const 2).mul ((h0.pow 2).add (h1.pow 2))).add
      ((h0.mul h1).div_const 2) |>.add
        ((h0.pow 2).div hden (mul_ne_zero (by norm_num) hx))
  have heq : besselEnergy =ᶠ[nhds x]
      (((fun y : ℝ => id y / 2) * (besselDerivative 0 ^ 2 + besselDerivative 1 ^ 2) +
          fun y => (besselDerivative 0 * besselDerivative 1) y / 2) +
        besselDerivative 0 ^ 2 / fun y => 4 * y) := by
    filter_upwards [] with y
    simp [besselEnergy]
  have hf := hraw.congr_of_eventuallyEq heq
  apply hf.congr_deriv
  apply sub_eq_zero.mp
  have hr := besselDerivative_recurrence 0 x
  simp only [Nat.cast_zero, zero_add, zero_mul, add_zero] at hr
  norm_num only [Nat.zero_add, Nat.one_add, pow_one, one_mul, id_eq, Pi.add_apply,
    Pi.mul_apply, Pi.pow_apply] at ⊢
  field_simp [hx]
  field_simp [hx] at hr
  have hzero : 2 * x * (2 * x * besselDerivative 1 x + besselDerivative 0 x) *
      (x * besselDerivative 2 x + besselDerivative 1 x + x * besselDerivative 0 x) = 0 := by
    rw [hr]
    ring
  nlinarith [hzero]

theorem besselEnergy_antitoneOn {a : ℝ} (ha : 0 < a) :
    AntitoneOn besselEnergy (Set.Ici a) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
  · intro x hx
    exact (hasDerivAt_besselEnergy (ne_of_gt (ha.trans_le hx))).continuousAt.continuousWithinAt
  · intro x hx
    have hax : a < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
    exact (hasDerivAt_besselEnergy (ne_of_gt (ha.trans hax))).hasDerivWithinAt
  · intro x hx
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

theorem besselEnergy_controls (x : ℝ) (hx : 0 < x) :
    x * besselDerivative 0 x ^ 2 / 2 ≤ besselEnergy x := by
  unfold besselEnergy
  have hs : 0 ≤ x / 2 * (besselDerivative 1 x + besselDerivative 0 x / (2*x)) ^ 2 := by
    positivity
  have ht : 0 ≤ besselDerivative 0 x ^ 2 / (8*x) := by positivity
  field_simp [ne_of_gt hx] at hs ht ⊢
  nlinarith

/-- The exact propagated grid values at `471 / 50` place the Sonin energy below `8 / 25`. -/
theorem besselEnergy_at_grid_start :
    2 * besselEnergy (3 * 157 / 50) ≤ (16 : ℝ) / 25 := by
  have hv := besselGridState003_valid
  unfold BesselStateValid besselGridState003 orderedInterval at hv
  simp only [LeanCert.Core.IntervalRat.mem_def] at hv
  unfold besselEnergy
  norm_num at hv ⊢
  nlinarith [sq_nonneg (besselDerivative 0 (471 / 50) + 1 / 5),
    sq_nonneg (besselDerivative 1 (471 / 50) + 1 / 5)]

/-- A deliberately rounded rational tail estimate.  Its slack is useful when all dual
coefficients are subsequently rounded to decimal rationals. -/
theorem abs_besselJ0_le_of_500_le {x : ℝ} (hx : 500 ≤ x) :
    |besselJ0 x| ≤ 73 / 2000 := by
  have hq : (3 * 157 / 50 : ℝ) ≤ x := by norm_num; linarith
  have hxpos : 0 < x := by linarith
  have hmono' := besselEnergy_antitoneOn (a := (3 * 157 / 50 : ℝ)) (by norm_num)
  have hmono : besselEnergy x ≤ besselEnergy (3 * 157 / 50 : ℝ) :=
    hmono' (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hq) hq
  have hcontrol := besselEnergy_controls x hxpos
  have hstart := besselEnergy_at_grid_start
  have hsquare : x * besselDerivative 0 x ^ 2 ≤ 16 / 25 := by nlinarith
  rw [besselJ0]
  have habs : |besselDerivative 0 x| ^ 2 = besselDerivative 0 x ^ 2 := sq_abs _
  have hnonneg := abs_nonneg (besselDerivative 0 x)
  rw [← habs] at hsquare
  nlinarith [sq_nonneg (|besselDerivative 0 x| - 73 / 2000)]

end Erdos232
