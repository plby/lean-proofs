/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.Path
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A quantitative endpoint for Erdős Problem 515

This file records the summability argument at the end of the Lewis--Rossi--Weitsman
construction.  It is intentionally independent of the potential-theoretic construction: any
polygonal ray whose `n`th segment has length at most `exp n` and on which the modulus is at
least `exp (n ^ 2)` has finite inverse-modulus arclength integral for every positive exponent.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Erdos515

private lemma natCast_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  rcases n with _ | n
  · norm_num
  simp only [Nat.cast_succ]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n : ℝ)]

private lemma summable_exp_sub_mul_sq {lambda : ℝ} (hlambda : 0 < lambda) :
    Summable (fun n : ℕ ↦ Real.exp ((n : ℝ) - lambda * (n : ℝ) ^ 2)) := by
  have hgauss : Summable
      (fun n : ℕ ↦ Real.exp (-(lambda / 2) * ((n : ℝ) ^ 2))) :=
    Real.summable_exp_nat_mul_of_ge (by linarith) natCast_le_sq
  refine (hgauss.mul_left (Real.exp (1 / (2 * lambda)))).of_nonneg_of_le
    (fun _ ↦ Real.exp_nonneg _) (fun n ↦ ?_)
  rw [← Real.exp_add]
  apply Real.exp_monotone
  have hsquare : 0 ≤ (lambda * (n : ℝ) - 1) ^ 2 := sq_nonneg _
  have hquot : 0 ≤ (lambda * (n : ℝ) - 1) ^ 2 / (2 * lambda) :=
    div_nonneg hsquare (mul_nonneg (by norm_num) hlambda.le)
  calc
    (n : ℝ) - lambda * (n : ℝ) ^ 2 =
        1 / (2 * lambda) + -(lambda / 2) * (n : ℝ) ^ 2 -
          (lambda * (n : ℝ) - 1) ^ 2 / (2 * lambda) := by
            field_simp [hlambda.ne']
            ring
    _ ≤ 1 / (2 * lambda) + -(lambda / 2) * (n : ℝ) ^ 2 :=
      sub_le_self _ hquot

/-- The real majorant used for the `n`th polygonal segment. -/
noncomputable def gaussianSegmentMajorant (lambda : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((n : ℝ) - lambda * (n : ℝ) ^ 2))

lemma tsum_gaussianSegmentMajorant_lt_top {lambda : ℝ} (hlambda : 0 < lambda) :
    ∑' n : ℕ, gaussianSegmentMajorant lambda n < ∞ := by
  rw [lt_top_iff_ne_top]
  let g : ℕ → ℝ≥0 := fun n ↦
    ⟨Real.exp ((n : ℝ) - lambda * (n : ℝ) ^ 2), Real.exp_nonneg _⟩
  have hfun : gaussianSegmentMajorant lambda = fun n ↦ (g n : ℝ≥0∞) := by
    funext n
    exact ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _)
  rw [hfun]
  change (∑' n : ℕ, (g n : ℝ≥0∞)) ≠ ∞
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  exact summable_exp_sub_mul_sq hlambda

/-- A pointwise lower modulus bound reverses after taking a negative real power. -/
lemma inverseNormDensity_le_of_exp_sq_le {f : ℂ → ℂ} {lambda : ℝ}
    (hlambda : 0 < lambda) {n : ℕ} {a b : ℂ} {t : ℝ}
    (hmod : Real.exp ((n : ℝ) ^ 2) ≤ ‖f (segmentPoint a b t)‖) :
    inverseNormDensity f lambda a b t ≤
      ENNReal.ofReal (Real.exp (-lambda * (n : ℝ) ^ 2)) := by
  rw [inverseNormDensity, ENNReal.ofReal_rpow_of_pos (lt_of_lt_of_le (Real.exp_pos _) hmod)]
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖f (segmentPoint a b t)‖ ^ (-lambda) ≤
        Real.exp ((n : ℝ) ^ 2) ^ (-lambda) :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hmod (by linarith)
    _ = Real.exp (-lambda * (n : ℝ) ^ 2) := by
      rw [← Real.exp_mul]
      ring_nf

/-- Under the standard quadratic growth and exponential length estimates, one segment is
bounded by the Gaussian majorant. -/
lemma segmentIntegral_le_gaussianSegmentMajorant {C : LocallyRectifiablePath}
    {f : ℂ → ℂ} {lambda : ℝ} (hlambda : 0 < lambda) {n : ℕ}
    (hlength : ‖C.vertex (n + 1) - C.vertex n‖ ≤ Real.exp n)
    (hmod : ∀ t ∈ Icc (0 : ℝ) 1,
      Real.exp ((n : ℝ) ^ 2) ≤
        ‖f (segmentPoint (C.vertex n) (C.vertex (n + 1)) t)‖) :
    segmentIntegral f lambda (C.vertex n) (C.vertex (n + 1)) ≤
      gaussianSegmentMajorant lambda n := by
  rw [segmentIntegral]
  calc
    ENNReal.ofReal ‖C.vertex (n + 1) - C.vertex n‖ *
          ∫⁻ t in Icc (0 : ℝ) 1,
            inverseNormDensity f lambda (C.vertex n) (C.vertex (n + 1)) t
        ≤ ENNReal.ofReal (Real.exp n) *
          ∫⁻ _t in Icc (0 : ℝ) 1,
            ENNReal.ofReal (Real.exp (-lambda * (n : ℝ) ^ 2)) := by
      have hint :
          (∫⁻ t in Icc (0 : ℝ) 1,
              inverseNormDensity f lambda (C.vertex n) (C.vertex (n + 1)) t) ≤
            ∫⁻ _t in Icc (0 : ℝ) 1,
              ENNReal.ofReal (Real.exp (-lambda * (n : ℝ) ^ 2)) := by
        refine setLIntegral_mono measurable_const (fun t ht ↦ ?_)
        exact inverseNormDensity_le_of_exp_sq_le hlambda (hmod t ht)
      exact mul_le_mul (ENNReal.ofReal_le_ofReal hlength) hint bot_le bot_le
    _ = gaussianSegmentMajorant lambda n := by
      rw [show (∫⁻ _t in Icc (0 : ℝ) 1,
          ENNReal.ofReal (Real.exp (-lambda * (n : ℝ) ^ 2))) =
            ENNReal.ofReal (Real.exp (-lambda * (n : ℝ) ^ 2)) by
        simp [Real.volume_Icc]]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      simp only [gaussianSegmentMajorant]
      congr 2
      ring

/-- Quantitative LRW endpoint: a single sufficiently fast-growth polygonal ray works for every
positive inverse power. -/
theorem lineIntegral_lt_top_of_quadratic_growth
    (C : LocallyRectifiablePath) (f : ℂ → ℂ)
    (hlength : ∀ n : ℕ, ‖C.vertex (n + 1) - C.vertex n‖ ≤ Real.exp n)
    (hmod : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
      Real.exp ((n : ℝ) ^ 2) ≤
        ‖f (segmentPoint (C.vertex n) (C.vertex (n + 1)) t)‖) :
    ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda < ∞ := by
  intro lambda hlambda
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n ↦ ?_))
    (tsum_gaussianSegmentMajorant_lt_top hlambda)
  exact segmentIntegral_le_gaussianSegmentMajorant hlambda (hlength n) (hmod n)

end Erdos515
