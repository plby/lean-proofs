/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CliqueRegularizationScalars

/-! # Explicit error transfer from original to reserve-protected clique extensions -/

namespace Erdos207

theorem reserve_clique_error_transfer
    (x y f xi delta r u : ℝ) (s : ℕ)
    (hx : 0 ≤ x) (hf : 0 ≤ f) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hxi : xi ≤ delta / 4) (hs : s ≤ 4) (hsf : (s : ℝ) ≤ delta * f / 4)
    (hu : u ≤ delta * f / 4) (hr : 0 ≤ r) (hrdelta : r ≤ delta / 64)
    (hold : |x - f| ≤ xi * f + s) (hmono : y ≤ x)
    (hloss : x ≤ y + u + 2 * s * r * x) : |y - f| ≤ delta * f := by
  have hxiF := mul_le_mul_of_nonneg_right hxi hf
  have hdeltaF := mul_le_mul_of_nonneg_right hdelta1 hf
  have hdeltaF0 : 0 ≤ delta * f := mul_nonneg hdelta hf
  have habs : |x - f| ≤ delta * f / 2 := by linarith
  have hold' := abs_le.mp habs
  have hx2 : x ≤ 2 * f := by linarith
  have hsR : (s : ℝ) ≤ 4 := by exact_mod_cast hs
  have hsx : (s : ℝ) * x ≤ 4 * (2 * f) := mul_le_mul hsR hx2 hx (by norm_num)
  have hrF := mul_le_mul_of_nonneg_right hrdelta hf
  have hspokes : 2 * (s : ℝ) * r * x ≤ delta * f / 4 := by
    calc
      _ = (2 * r) * ((s : ℝ) * x) := by ring
      _ ≤ (2 * r) * (4 * (2 * f)) := mul_le_mul_of_nonneg_left hsx (by positivity)
      _ ≤ delta * f / 4 := by nlinarith
  apply abs_le.mpr
  constructor <;> linarith

theorem reserve_clique_regularization_margins
    (x y f xi r u : ℝ) (s : ℕ)
    (hx : 0 ≤ x) (hf : 6144 ≤ f) (hxi : xi ≤ 1 / 1536) (hs : s ≤ 4)
    (hu : u ≤ f / 1536) (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 24576)
    (hold : |x - f| ≤ xi * f + s) (hmono : y ≤ x)
    (hloss : x ≤ y + u + 2 * s * r * x) :
    |f - y| ≤ f / (12 * (2 : ℝ) ^ 5) ∧ f / 2 ≤ y ∧ y ≤ 2 * f := by
  have hsR : (s : ℝ) ≤ 4 := by exact_mod_cast hs
  have h := reserve_clique_error_transfer x y f xi (1 / 384) r u s hx (by linarith)
    (by norm_num) (by norm_num) (by norm_num; exact hxi) hs
    (by nlinarith) (by nlinarith) hr (by norm_num; exact hrsmall) hold hmono hloss
  have hb := abs_le.mp h
  constructor
  · rw [abs_sub_comm]
    norm_num
    nlinarith
  · constructor <;> nlinarith

end Erdos207
