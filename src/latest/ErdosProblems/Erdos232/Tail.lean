/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.Energy
import ErdosProblems.Erdos232.CertificateData

/-!
# The infinite part of the Erdős--232 spectral certificate

The Sonin-energy estimate from `Energy` bounds each Bessel term after its argument has
passed `471 / 50`.  This file combines that analytic estimate with exact rational lower
bounds for the twenty-seven certificate distances.  The deliberately outward-rounded
decimal bounds leave a small, exactly checked margin in the final weighted sum.
-/

open LeanCert.Core

namespace Erdos232

/-- The Sonin energy gives the scale-sensitive estimate used in the tail. -/
theorem mul_sq_besselJ0_le_of_grid_start {x : ℝ} (hx : 3 * 157 / 50 ≤ x) :
    x * besselJ0 x ^ 2 ≤ 16 / 25 := by
  have hxpos : 0 < x := by norm_num at hx ⊢; linarith
  have hmono' := besselEnergy_antitoneOn (a := (3 * 157 / 50 : ℝ)) (by norm_num)
  have hmono : besselEnergy x ≤ besselEnergy (3 * 157 / 50 : ℝ) :=
    hmono' (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  have hcontrol := besselEnergy_controls x hxpos
  have hstart := besselEnergy_at_grid_start
  rw [besselJ0]
  nlinarith

/-- A convenient square-root-free consequence of the Sonin estimate. -/
theorem abs_besselJ0_le_of_scale {x L c : ℝ}
    (hx : 3 * 157 / 50 ≤ x) (hL : L ≤ x) (hL0 : 0 ≤ L) (hc : 0 ≤ c)
    (hLc : 16 / 25 ≤ L * c ^ 2) :
    |besselJ0 x| ≤ c := by
  have hx0 : 0 ≤ x := hL0.trans hL
  have hb := mul_sq_besselJ0_le_of_grid_start hx
  have hs : |besselJ0 x| ^ 2 = besselJ0 x ^ 2 := sq_abs _
  rw [← hs] at hb
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hxc : L * c ^ 2 ≤ x * c ^ 2 := mul_le_mul_of_nonneg_right hL hc2
  nlinarith [sq_nonneg (|besselJ0 x| - c)]

/-- Rational upper bounds for the absolute values of the twenty-seven Bessel terms on
the half-line `t ≥ 500`. -/
def dualTailBound (i : Fin 27) : ℚ :=
  match i.val with
  | 0 => 36500 / 1000000
  | 1 => 42529 / 1000000
  | 2 => 33446 / 1000000
  | 3 => 78730 / 1000000
  | 4 => 48037 / 1000000
  | 5 => 29153 / 1000000
  | 6 => 33968 / 1000000
  | 7 => 25949 / 1000000
  | 8 => 30235 / 1000000
  | 9 => 24410 / 1000000
  | 10 => 32125 / 1000000
  | 11 => 24116 / 1000000
  | 12 => 24949 / 1000000
  | 13 => 29533 / 1000000
  | 14 => 27735 / 1000000
  | 15 => 30375 / 1000000
  | 16 => 32315 / 1000000
  | 17 => 26844 / 1000000
  | 18 => 36091 / 1000000
  | 19 => 39199 / 1000000
  | 20 => 49553 / 1000000
  | 21 => 67570 / 1000000
  | 22 => 41007 / 1000000
  | 23 => 35093 / 1000000
  | 24 => 53968 / 1000000
  | 25 => 26768 / 1000000
  | _ => 32752 / 1000000

private theorem dualDistance_lower_mul_tailBound_sq (i : Fin 27) :
    (16 : ℚ) / 25 ≤ 500 * (dualDistanceInterval i).lo * dualTailBound i ^ 2 := by
  fin_cases i <;>
    norm_num [dualDistanceInterval, dualTailBound, orderedInterval]

private theorem dualDistanceInterval_lo_nonneg (i : Fin 27) :
    (0 : ℚ) ≤ (dualDistanceInterval i).lo := by
  fin_cases i <;> norm_num [dualDistanceInterval, orderedInterval]

/-- Every individual Bessel term is bounded by its exact rational tail allowance. -/
theorem abs_besselJ0_mul_dualDistance_le (i : Fin 27) {t : ℝ} (ht : 500 ≤ t) :
    |besselJ0 (t * dualDistance i)| ≤ (dualTailBound i : ℝ) := by
  have hd := (dualDistance_mem i).1
  have hlo0 : (0 : ℝ) ≤ ((dualDistanceInterval i).lo : ℚ) := by
    exact_mod_cast dualDistanceInterval_lo_nonneg i
  have hd0 : 0 ≤ dualDistance i := hlo0.trans hd
  have hprod : (500 : ℝ) * ((dualDistanceInterval i).lo : ℚ) ≤
      t * dualDistance i := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hd0,
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 500) (sub_nonneg.mpr hd)]
  apply abs_besselJ0_le_of_scale
      (L := (500 : ℝ) * ((dualDistanceInterval i).lo : ℚ))
  · have hstart : (3 * 157 / 50 : ℝ) ≤
        500 * ((dualDistanceInterval i).lo : ℚ) := by
      fin_cases i <;> norm_num [dualDistanceInterval, orderedInterval]
    exact hstart.trans hprod
  · exact hprod
  · positivity
  · exact_mod_cast (show (0 : ℚ) ≤ dualTailBound i by
      fin_cases i <;> norm_num [dualTailBound])
  · have hq := dualDistance_lower_mul_tailBound_sq i
    have hr : (((16 : ℚ) / 25 : ℚ) : ℝ) ≤
        ((500 * (dualDistanceInterval i).lo * dualTailBound i ^ 2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hq
    push_cast at hr
    norm_num at hr ⊢
    exact hr

/-- The weighted absolute-error allowance in the tail is smaller than the constant
coefficient's excess above one. -/
theorem dual_tail_arithmetic :
    (1 : ℚ) + (∑ i : Fin 27, |dualWeight i| * dualTailBound i) ≤ dualConstant := by
  norm_num [dualWeight, dualTailBound, dualConstant, Fin.sum_univ_succ]

/-- The complete dual spectral function is at least one on the unbounded tail. -/
theorem dual_spectral_tail {t : ℝ} (ht : 500 ≤ t) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  have habs : ∀ i : Fin 27,
      |(dualWeight i : ℝ) * besselJ0 (t * dualDistance i)| ≤
        ((|dualWeight i| * dualTailBound i : ℚ) : ℝ) := by
    intro i
    rw [abs_mul]
    push_cast
    exact mul_le_mul_of_nonneg_left (abs_besselJ0_mul_dualDistance_le i ht) (abs_nonneg _)
  have hsum :
      -(∑ i : Fin 27, ((|dualWeight i| * dualTailBound i : ℚ) : ℝ)) ≤
        spectralSum dualWeight dualDistance t := by
    rw [spectralSum]
    calc
      -(∑ i : Fin 27, ((|dualWeight i| * dualTailBound i : ℚ) : ℝ))
          ≤ ∑ i : Fin 27, -|(dualWeight i : ℝ) *
              besselJ0 (t * dualDistance i)| := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_le_sum fun i _ => neg_le_neg (habs i)
      _ ≤ ∑ i : Fin 27, (dualWeight i : ℝ) *
            besselJ0 (t * dualDistance i) :=
        Finset.sum_le_sum fun i _ => neg_abs_le _
  have harith :
      (1 : ℝ) + ∑ i : Fin 27, ((|dualWeight i| * dualTailBound i : ℚ) : ℝ) ≤
        (dualConstant : ℝ) := by
    exact_mod_cast dual_tail_arithmetic
  linarith

end Erdos232
