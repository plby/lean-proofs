/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterParameters

/-!
# Thin-annulus geometry in Hunter's construction

The midpoint identity in a real inner-product space implies that three
equally spaced points in one radial shell have very small common difference.
This file proves the estimate with explicit constants and then specializes
the shell width to the integral parameter sequence.
-/

namespace Erdos721.HunterAnnulus

open Set Real

/-- The radial thickness `N^(-4/D)` after substituting Hunter's integral
ambient length `N = D^(D²/200)`. -/
noncomputable def shellWidth (D : ℕ) : ℝ :=
  ((D ^ (D / 50) : ℕ) : ℝ)⁻¹

/-- The exceptional common-difference scale `N^(-2/D) / 2`. -/
noncomputable def stepThreshold (D : ℕ) : ℝ :=
  (2 * ((D ^ (D / 100) : ℕ) : ℝ))⁻¹

/-- A half-open Euclidean radial shell. -/
def shell {E : Type*} [SeminormedAddCommGroup E]
    (q : ℝ) (k : ℕ) : Set E :=
  {x | (k : ℝ) * q ≤ ‖x‖ ∧ ‖x‖ < (k + 1 : ℕ) * q}

lemma mem_shell_iff {E : Type*} [SeminormedAddCommGroup E]
    {q : ℝ} {k : ℕ} {x : E} :
    x ∈ shell q k ↔ (k : ℝ) * q ≤ ‖x‖ ∧ ‖x‖ < (k + 1 : ℕ) * q :=
  Iff.rfl

lemma shellWidth_pos {D : ℕ} (hD : 0 < D) : 0 < shellWidth D := by
  exact inv_pos.mpr (by positivity)

lemma shellWidth_nonneg (D : ℕ) : 0 ≤ shellWidth D := by
  exact inv_nonneg.mpr (by positivity)

lemma stepThreshold_pos {D : ℕ} (hD : 0 < D) : 0 < stepThreshold D := by
  exact inv_pos.mpr (by positivity)

lemma stepThreshold_sq {D : ℕ} (hD : 0 < D)
    (hdiv : 100 ∣ D) :
    stepThreshold D ^ 2 = shellWidth D / 4 := by
  obtain ⟨m, rfl⟩ := hdiv
  have hm : 0 < m := by
    by_contra hm0
    simp_all
  simp only [stepThreshold, shellWidth]
  norm_num only [Nat.mul_div_cancel_left]
  push_cast
  rw [show (100 * m) / 50 = 2 * m by omega,
    show 2 * m = m * 2 by omega, pow_mul]
  field_simp
  ring

/-- Quantitative midpoint geometry.  If `u`, `u+v`, and `u+2v` all have
norm in `[r,r+q)`, then `‖v‖² < 2rq+q²`. -/
lemma norm_step_sq_lt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u v : E} {r q : ℝ}
    (hr : 0 ≤ r) (hq : 0 < q)
    (hu_lower : r ≤ ‖u‖) (hu_upper : ‖u‖ < r + q)
    (hm_lower : r ≤ ‖u + v‖) (hm_upper : ‖u + v‖ < r + q)
    (hw_lower : r ≤ ‖u + v + v‖)
    (hw_upper : ‖u + v + v‖ < r + q) :
    ‖v‖ ^ 2 < 2 * r * q + q ^ 2 := by
  have hpara := parallelogram_law_with_norm ℝ (u + v) v
  have hidentity :
      ‖u + v + v‖ ^ 2 + ‖u‖ ^ 2 =
        2 * (‖u + v‖ ^ 2 + ‖v‖ ^ 2) := by
    simpa only [add_assoc, add_sub_cancel_right] using hpara
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hm0 : 0 ≤ ‖u + v‖ := norm_nonneg _
  have hw0 : 0 ≤ ‖u + v + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - r), sq_nonneg (‖u + v‖ - r),
    sq_nonneg (‖u + v + v‖ - r), sq_nonneg (r + q - ‖u‖),
    sq_nonneg (r + q - ‖u + v‖),
    sq_nonneg (r + q - ‖u + v + v‖)]

/-- Three equally spaced points in one shell have squared step smaller than
`q * (2 k q + q)`. -/
lemma norm_step_sq_lt_of_mem_shell {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u v : E} {q : ℝ} {k : ℕ}
    (hq : 0 < q)
    (hu : u ∈ shell q k) (hm : u + v ∈ shell q k)
    (hw : u + v + v ∈ shell q k) :
    ‖v‖ ^ 2 < q * (2 * (k : ℝ) * q + q) := by
  rw [mem_shell_iff] at hu hm hw
  have hu_upper : ‖u‖ < (k : ℝ) * q + q := by
    norm_num at hu
    nlinarith [hu.2]
  have hm_upper : ‖u + v‖ < (k : ℝ) * q + q := by
    norm_num at hm
    nlinarith [hm.2]
  have hw_upper : ‖u + v + v‖ < (k : ℝ) * q + q := by
    norm_num at hw
    nlinarith [hw.2]
  have h := norm_step_sq_lt
    (r := (k : ℝ) * q) (q := q)
    (mul_nonneg (by positivity) hq.le) hq
    hu.1 hu_upper hm.1 hm_upper hw.1 hw_upper
  nlinarith

/-- Hunter's numerical condition turns the preceding squared estimate into
the exceptional step threshold `sqrt(q)/2`. -/
lemma norm_step_lt_half_sqrt_of_mem_shell {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} {q : ℝ} {k : ℕ} (hq : 0 < q)
    (houter : 2 * (k : ℝ) * q + q ≤ 1 / 4)
    (hu : u ∈ shell q k) (hm : u + v ∈ shell q k)
    (hw : u + v + v ∈ shell q k) :
    ‖v‖ < Real.sqrt q / 2 := by
  have hsq := norm_step_sq_lt_of_mem_shell hq hu hm hw
  have hmul := mul_le_mul_of_nonneg_left houter hq.le
  have hq4 : ‖v‖ ^ 2 < q / 4 := hsq.trans_le (by nlinarith)
  have hsqrt0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hsqrteq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
  nlinarith

end Erdos721.HunterAnnulus
