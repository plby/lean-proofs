/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Parameters for the Joos--Mubayi upper construction

This file contains the analytic bookkeeping which is independent of the
finite auxiliary-hypergraph construction.  Starting with the small constant
provided by the conflict-free matching theorem, we choose a positive
`delta`, put `rho = n⁻ᵟ`, and define the retained/deleted probabilities

`p = rho / (1 + rho)` and `q = 1 / (1 + rho)`.  In the source, `p` is the
small absence probability and `q` is the large retained/present probability.

The old and fresh palettes are the two ceilings used in the construction.
The final theorem proves, including the rounding errors, that their sum is
`(5/6 + o(1)) n`.  We also record the degree scale `n^(3-delta)`, the CFM
relative error, fixed-threshold extraction, and the numerical expression
which occurs in the symmetric local-lemma check.
-/

namespace Erdos136

open Filter
open scoped Topology

noncomputable section

/-! ## Choice of fixed exponents -/

/-- The conflict-free matching exponent, chosen below both its supplied
threshold and a fixed small absolute constant. -/
def jmEta (eta0 : ℝ) : ℝ := min (eta0 / 2) (1 / 100)

/-- The construction exponent is much smaller than `eta^3`; this is the
hierarchy needed for the CFM error to dominate all `n^(-2*delta)` errors. -/
def jmDelta (eta0 : ℝ) : ℝ :=
  min ((jmEta eta0) ^ 3 / 100) (1 / 10000)

theorem jmEta_pos {eta0 : ℝ} (h : 0 < eta0) : 0 < jmEta eta0 := by
  unfold jmEta
  exact lt_min (div_pos h (by norm_num)) (by norm_num)

theorem jmEta_lt_threshold {eta0 : ℝ} (h : 0 < eta0) :
    jmEta eta0 < eta0 := by
  have heta : jmEta eta0 ≤ eta0 / 2 := min_le_left _ _
  nlinarith

theorem jmEta_lt_one {eta0 : ℝ} (_h : 0 < eta0) : jmEta eta0 < 1 := by
  have heta : jmEta eta0 ≤ (1 / 100 : ℝ) := min_le_right _ _
  norm_num at heta ⊢
  linarith

theorem jmDelta_pos {eta0 : ℝ} (h : 0 < eta0) : 0 < jmDelta eta0 := by
  unfold jmDelta
  exact lt_min (div_pos (pow_pos (jmEta_pos h) 3) (by norm_num)) (by norm_num)

theorem jmDelta_le_one_ten_thousandth (eta0 : ℝ) :
    jmDelta eta0 ≤ (1 / 10000 : ℝ) := by
  exact min_le_right _ _

theorem jmDelta_lt_one {eta0 : ℝ} (_h : 0 < eta0) : jmDelta eta0 < 1 := by
  exact (jmDelta_le_one_ten_thousandth eta0).trans_lt (by norm_num)

/-- The main exponent hierarchy used in the tracked estimates. -/
theorem jm_two_delta_lt_eta_cube {eta0 : ℝ} (h : 0 < eta0) :
    2 * jmDelta eta0 < (jmEta eta0) ^ 3 := by
  have hd : jmDelta eta0 ≤ (jmEta eta0) ^ 3 / 100 := min_le_left _ _
  have he : 0 < (jmEta eta0) ^ 3 := pow_pos (jmEta_pos h) 3
  nlinarith

/-- Since `3 - delta > 2`, the CFM exponent on the degree scale is still
strictly larger than `2 * delta`. -/
theorem jm_two_delta_lt_degree_exponent {eta0 : ℝ} (h : 0 < eta0) :
    2 * jmDelta eta0 < (3 - jmDelta eta0) * (jmEta eta0) ^ 3 := by
  have hd1 := jmDelta_lt_one h
  have he : 0 < (jmEta eta0) ^ 3 := pow_pos (jmEta_pos h) 3
  have hh := jm_two_delta_lt_eta_cube h
  nlinarith [mul_pos (by linarith : 0 < 2 - jmDelta eta0) he]

/-! ## Retention probabilities -/

/-- The small perturbation parameter `rho = n⁻ᵟ`. -/
def jmRho (delta : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-delta)

/-- The small absence probability `p`.  The identifier is retained for
compatibility with the first draft of this development; this is *not* the
source's retained/present probability. -/
def jmRetention (delta : ℝ) (n : ℕ) : ℝ :=
  jmRho delta n / (1 + jmRho delta n)

/-- The large retained/present probability `q`.  The source calls this the
retention probability; it is complementary to `jmRetention`. -/
def jmDeletion (delta : ℝ) (n : ℕ) : ℝ :=
  1 / (1 + jmRho delta n)

theorem jmRho_pos {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    0 < jmRho delta n := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem jmRetention_pos {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    0 < jmRetention delta n := by
  unfold jmRetention
  have hr := jmRho_pos (delta := delta) hn
  exact div_pos hr (by linarith)

theorem jmRetention_lt_one {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmRetention delta n < 1 := by
  unfold jmRetention
  have hr := jmRho_pos (delta := delta) hn
  exact (div_lt_one (by positivity)).2 (by linarith)

theorem jmDeletion_pos {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    0 < jmDeletion delta n := by
  unfold jmDeletion
  have hr := jmRho_pos (delta := delta) hn
  exact div_pos zero_lt_one (by linarith)

theorem jmDeletion_lt_one {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmDeletion delta n < 1 := by
  unfold jmDeletion
  have hr := jmRho_pos (delta := delta) hn
  exact (div_lt_one (by positivity)).2 (by linarith)

theorem jmRetention_add_deletion {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmRetention delta n + jmDeletion delta n = 1 := by
  unfold jmRetention jmDeletion
  have hr := jmRho_pos (delta := delta) hn
  field_simp
  ring

/-- The large retained probability is exactly `q = 1 - p`. -/
theorem jmDeletion_eq_one_sub_retention {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmDeletion delta n = 1 - jmRetention delta n := by
  linarith [jmRetention_add_deletion (delta := delta) hn]

theorem jmRho_tendsto_zero {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (jmRho delta) atTop (nhds 0) := by
  exact (tendsto_rpow_neg_atTop hdelta).comp tendsto_natCast_atTop_atTop

theorem jmRetention_tendsto_zero {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (jmRetention delta) atTop (nhds 0) := by
  have hrho := jmRho_tendsto_zero hdelta
  have hden : Tendsto (fun n : ℕ => 1 + jmRho delta n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hrho
  change Tendsto (fun n : ℕ => jmRho delta n / (1 + jmRho delta n))
    atTop (nhds 0)
  have hquot := hrho.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (jmRho delta / fun n : ℕ => 1 + jmRho delta n) =ᶠ[atTop]
      fun n => jmRho delta n / (1 + jmRho delta n) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  simpa only [zero_div] using hquot.congr' heq

theorem jmDeletion_tendsto_one {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (jmDeletion delta) atTop (nhds 1) := by
  have hrho := jmRho_tendsto_zero hdelta
  have hden : Tendsto (fun n : ℕ => 1 + jmRho delta n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hrho
  change Tendsto (fun n : ℕ => 1 / (1 + jmRho delta n))
    atTop (nhds 1)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hquot := hone.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have heq : ((fun _ : ℕ => (1 : ℝ)) / fun n => 1 + jmRho delta n) =ᶠ[atTop]
      fun n => 1 / (1 + jmRho delta n) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  simpa only [one_div, div_one] using hquot.congr' heq

theorem eventually_half_le_jmDeletion {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ jmDeletion delta n := by
  exact (jmDeletion_tendsto_one hdelta).eventually_const_le (by norm_num)

/-! ## Palette sizes and rounding -/

/-- The unrounded old palette size `(1 + rho) 5n/6`. -/
def jmOldPaletteReal (delta : ℝ) (n : ℕ) : ℝ :=
  (5 / 6 : ℝ) * (n : ℝ) * (1 + jmRho delta n)

/-- The number of old colours in the finite construction. -/
def jmOldColors (delta : ℝ) (n : ℕ) : ℕ :=
  ⌈jmOldPaletteReal delta n⌉₊

/-- The unrounded fresh palette size `n^(1-delta)`. -/
def jmFreshPaletteReal (delta : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 - delta)

/-- The number of fresh colours reserved for the leave. -/
def jmFreshColors (delta : ℝ) (n : ℕ) : ℕ :=
  ⌈jmFreshPaletteReal delta n⌉₊

/-- Total number of colours used after completing the sparse leave. -/
def jmTotalColors (delta : ℝ) (n : ℕ) : ℕ :=
  jmOldColors delta n + jmFreshColors delta n

theorem jmOldPaletteReal_nonneg (delta : ℝ) (n : ℕ) :
    0 ≤ jmOldPaletteReal delta n := by
  unfold jmOldPaletteReal
  have hr : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  positivity

theorem jmFreshPaletteReal_nonneg (delta : ℝ) (n : ℕ) :
    0 ≤ jmFreshPaletteReal delta n := by
  unfold jmFreshPaletteReal
  positivity

theorem jmOldPaletteReal_le_colors (delta : ℝ) (n : ℕ) :
    jmOldPaletteReal delta n ≤ (jmOldColors delta n : ℝ) := by
  exact Nat.le_ceil _

theorem jmOldColors_lt_add_one (delta : ℝ) (n : ℕ) :
    (jmOldColors delta n : ℝ) < jmOldPaletteReal delta n + 1 := by
  exact Nat.ceil_lt_add_one (jmOldPaletteReal_nonneg delta n)

theorem jmFreshPaletteReal_le_colors (delta : ℝ) (n : ℕ) :
    jmFreshPaletteReal delta n ≤ (jmFreshColors delta n : ℝ) := by
  exact Nat.le_ceil _

theorem jmFreshColors_lt_add_one (delta : ℝ) (n : ℕ) :
    (jmFreshColors delta n : ℝ) < jmFreshPaletteReal delta n + 1 := by
  exact Nat.ceil_lt_add_one (jmFreshPaletteReal_nonneg delta n)

theorem jmTotalColors_upper (delta : ℝ) (n : ℕ) :
    (jmTotalColors delta n : ℝ) <
      jmOldPaletteReal delta n + jmFreshPaletteReal delta n + 2 := by
  rw [jmTotalColors, Nat.cast_add]
  linarith [jmOldColors_lt_add_one delta n,
    jmFreshColors_lt_add_one delta n]

theorem jmFresh_div {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmFreshPaletteReal delta n / (n : ℝ) = jmRho delta n := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply (div_eq_iff hnreal.ne').2
  unfold jmFreshPaletteReal jmRho
  calc
    (n : ℝ) ^ (1 - delta) = (n : ℝ) ^ (-delta + 1) := by ring_nf
    _ = (n : ℝ) ^ (-delta) * (n : ℝ) ^ (1 : ℝ) :=
      Real.rpow_add hnreal _ _
    _ = (n : ℝ) ^ (-delta) * (n : ℝ) := by
      rw [Real.rpow_one]

/-- An explicit normalized upper envelope, including both ceiling errors. -/
def jmNormalizedUpper (delta : ℝ) (n : ℕ) : ℝ :=
  (5 / 6 : ℝ) * (1 + jmRho delta n) + jmRho delta n +
    2 * (n : ℝ)⁻¹

theorem jmTotalColors_normalized_upper {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    (jmTotalColors delta n : ℝ) / (n : ℝ) ≤ jmNormalizedUpper delta n := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdiv : (jmTotalColors delta n : ℝ) / (n : ℝ) <
      (jmOldPaletteReal delta n + jmFreshPaletteReal delta n + 2) /
        (n : ℝ) :=
    (div_lt_div_iff_of_pos_right hnreal).2 (jmTotalColors_upper delta n)
  apply le_of_lt
  calc
    (jmTotalColors delta n : ℝ) / (n : ℝ) <
        (jmOldPaletteReal delta n + jmFreshPaletteReal delta n + 2) /
          (n : ℝ) := hdiv
    _ = jmNormalizedUpper delta n := by
      rw [add_div, add_div, jmFresh_div hn]
      unfold jmOldPaletteReal jmNormalizedUpper
      field_simp

theorem jmTotalColors_normalized_lower {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    (5 / 6 : ℝ) * (1 + jmRho delta n) ≤
      (jmTotalColors delta n : ℝ) / (n : ℝ) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply (le_div_iff₀ hnreal).2
  calc
    (5 / 6 : ℝ) * (1 + jmRho delta n) * (n : ℝ) =
        jmOldPaletteReal delta n := by
          unfold jmOldPaletteReal
          ring
    _ ≤ (jmOldColors delta n : ℝ) := jmOldPaletteReal_le_colors delta n
    _ ≤ (jmTotalColors delta n : ℝ) := by
      rw [jmTotalColors, Nat.cast_add]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)

theorem jmNormalizedUpper_tendsto {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (jmNormalizedUpper delta) atTop (nhds (5 / 6 : ℝ)) := by
  have hrho := jmRho_tendsto_zero hdelta
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  unfold jmNormalizedUpper
  convert ((tendsto_const_nhds.mul (tendsto_const_nhds.add hrho)).add hrho).add
      (tendsto_const_nhds.mul hinv) using 1 <;> norm_num

/-- The exact old-plus-fresh palette, with natural-number ceilings, has the
required normalized limit. -/
theorem jmTotalColors_tendsto {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun n : ℕ => (jmTotalColors delta n : ℝ) / (n : ℝ)) atTop
      (nhds (5 / 6 : ℝ)) := by
  have hlower : Tendsto (fun n : ℕ =>
      (5 / 6 : ℝ) * (1 + jmRho delta n)) atTop (nhds (5 / 6 : ℝ)) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.add
      (jmRho_tendsto_zero hdelta)) using 1 <;> norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower
    (jmNormalizedUpper_tendsto hdelta)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact jmTotalColors_normalized_lower hn
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact jmTotalColors_normalized_upper hn

theorem eventually_jmTotalColors_ratio_le_add
    {delta epsilon : ℝ} (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      (jmTotalColors delta n : ℝ) / (n : ℝ) ≤ (5 / 6 : ℝ) + epsilon := by
  exact (jmTotalColors_tendsto hdelta).eventually_le_const (by linarith)

/-- Explicit additive `o(n)` error which absorbs both palette ceilings. -/
def jmPaletteUpperError (delta : ℝ) (n : ℕ) : ℝ :=
  (5 / 6 : ℝ) * (n : ℝ) * jmRho delta n +
    jmFreshPaletteReal delta n + 2

theorem jmTotalColors_le_main_add_error (delta : ℝ) (n : ℕ) :
    (jmTotalColors delta n : ℝ) ≤
      (5 / 6 : ℝ) * (n : ℝ) + jmPaletteUpperError delta n := by
  calc
    (jmTotalColors delta n : ℝ) ≤
        jmOldPaletteReal delta n + jmFreshPaletteReal delta n + 2 :=
      (jmTotalColors_upper delta n).le
    _ = (5 / 6 : ℝ) * (n : ℝ) + jmPaletteUpperError delta n := by
      unfold jmOldPaletteReal jmPaletteUpperError
      ring

theorem jmPaletteUpperError_div {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmPaletteUpperError delta n / (n : ℝ) =
      (5 / 6 : ℝ) * jmRho delta n + jmRho delta n +
        2 * (n : ℝ)⁻¹ := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [jmPaletteUpperError, add_div, add_div, jmFresh_div hn]
  field_simp

theorem jmPaletteUpperError_normalized_tendsto_zero
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun n : ℕ => jmPaletteUpperError delta n / (n : ℝ))
      atTop (nhds 0) := by
  have hrho := jmRho_tendsto_zero hdelta
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hmodel : Tendsto (fun n : ℕ =>
      (5 / 6 : ℝ) * jmRho delta n + jmRho delta n +
        2 * (n : ℝ)⁻¹) atTop (nhds 0) := by
    convert ((tendsto_const_nhds.mul hrho).add hrho).add
      (tendsto_const_nhds.mul hinv) using 1 <;> norm_num
  refine hmodel.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (jmPaletteUpperError_div hn).symm

/-- Literal asymptotic notation for the preceding normalized estimate. -/
theorem jmPaletteUpperError_isLittleO {delta : ℝ} (hdelta : 0 < delta) :
    (fun n : ℕ => jmPaletteUpperError delta n) =o[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).2
    (jmPaletteUpperError_normalized_tendsto_zero hdelta)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn hzero
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn) hzero).elim

/-! ## Degree and error scales -/

/-- The common auxiliary degree scale, up to a fixed positive constant. -/
def jmDegreeScale (delta : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (3 - delta)

/-- A natural upper degree parameter when an integral value is convenient. -/
def jmDegreeScaleNat (delta : ℝ) (n : ℕ) : ℕ :=
  ⌈jmDegreeScale delta n⌉₊

theorem jmDegreeScale_tendsto_atTop {delta : ℝ} (hdelta : delta < 3) :
    Tendsto (jmDegreeScale delta) atTop atTop := by
  exact (tendsto_rpow_atTop (sub_pos.mpr hdelta)).comp
    tendsto_natCast_atTop_atTop

theorem eventually_jmDegreeScale_ge {delta d0 : ℝ} (hdelta : delta < 3) :
    ∀ᶠ n : ℕ in atTop, d0 ≤ jmDegreeScale delta n :=
  (jmDegreeScale_tendsto_atTop hdelta) (eventually_ge_atTop d0)

theorem jmDegreeScaleNat_tendsto_atTop {delta : ℝ} (hdelta : delta < 3) :
    Tendsto (jmDegreeScaleNat delta) atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp (jmDegreeScale_tendsto_atTop hdelta)

/-- Rounding the degree scale changes it only by a relative `1 + o(1)`. -/
theorem jmDegreeScaleNat_ratio_tendsto_one {delta : ℝ} (hdelta : delta < 3) :
    Tendsto (fun n : ℕ =>
      (jmDegreeScaleNat delta n : ℝ) / jmDegreeScale delta n)
      atTop (nhds 1) := by
  exact tendsto_nat_ceil_div_atTop.comp (jmDegreeScale_tendsto_atTop hdelta)

/-- The central auxiliary degree before concentration, with the exact
constants and retention probabilities from the Joos--Mubayi construction. -/
def jmAuxDegreeReal (delta : ℝ) (n : ℕ) : ℝ :=
  (5 / 2 : ℝ) * (n : ℝ) ^ 2 * jmOldPaletteReal delta n *
    (jmDeletion delta n) ^ 4 * jmRetention delta n

theorem jm_cube_mul_rho {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 3 * jmRho delta n = jmDegreeScale delta n := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold jmRho jmDegreeScale
  rw [← Real.rpow_natCast, ← Real.rpow_add hnreal]
  congr 1

/-- Exact cancellation of `(1 + rho)` between the old palette and `p`.
Consequently the central degree is a fixed positive multiple of
`n^(3-delta)`, times `q^4`. -/
theorem jmAuxDegreeReal_eq {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmAuxDegreeReal delta n =
      (25 / 12 : ℝ) * jmDegreeScale delta n * (jmDeletion delta n) ^ 4 := by
  have hr := jmRho_pos (delta := delta) hn
  have hden : 1 + jmRho delta n ≠ 0 := by positivity
  calc
    jmAuxDegreeReal delta n =
        (25 / 12 : ℝ) * ((n : ℝ) ^ 3 * jmRho delta n) *
          (jmDeletion delta n) ^ 4 := by
      unfold jmAuxDegreeReal jmOldPaletteReal jmRetention jmDeletion
      field_simp [hden]
      ring
    _ = (25 / 12 : ℝ) * jmDegreeScale delta n *
          (jmDeletion delta n) ^ 4 := by rw [jm_cube_mul_rho hn]

theorem jmAuxDegreeReal_ratio {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmAuxDegreeReal delta n / jmDegreeScale delta n =
      (25 / 12 : ℝ) * (jmDeletion delta n) ^ 4 := by
  rw [jmAuxDegreeReal_eq hn]
  have hs : jmDegreeScale delta n ≠ 0 := by
    unfold jmDegreeScale
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).ne'
  field_simp

/-- This is the precise `d = Theta(n^(3-delta))` calculation. -/
theorem jmAuxDegreeReal_ratio_tendsto {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun n : ℕ =>
      jmAuxDegreeReal delta n / jmDegreeScale delta n) atTop
      (nhds (25 / 12 : ℝ)) := by
  have hmodel : Tendsto (fun n : ℕ =>
      (25 / 12 : ℝ) * (jmDeletion delta n) ^ 4) atTop
      (nhds (25 / 12 : ℝ)) := by
    have hq4 : Tendsto (fun n : ℕ => (jmDeletion delta n) ^ 4) atTop
        (nhds ((1 : ℝ) ^ 4)) := (jmDeletion_tendsto_one hdelta).pow 4
    have hc : Tendsto (fun _ : ℕ => (25 / 12 : ℝ)) atTop
        (nhds (25 / 12 : ℝ)) := tendsto_const_nhds
    convert hc.mul hq4 using 1 <;> norm_num
  refine hmodel.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (jmAuxDegreeReal_ratio hn).symm

theorem eventually_jmAuxDegreeReal_ge {delta d0 : ℝ}
    (hdelta0 : 0 < delta) (hdelta3 : delta < 3) :
    ∀ᶠ n : ℕ in atTop, d0 ≤ jmAuxDegreeReal delta n := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ jmAuxDegreeReal delta n / jmDegreeScale delta n :=
    (jmAuxDegreeReal_ratio_tendsto hdelta0).eventually_const_le (by norm_num)
  filter_upwards [eventually_jmDegreeScale_ge (d0 := d0) hdelta3,
    hratio, eventually_gt_atTop (0 : ℕ)] with n hd hratio hn
  have hspos : 0 < jmDegreeScale delta n := by
    unfold jmDegreeScale
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hsle : jmDegreeScale delta n ≤ jmAuxDegreeReal delta n := by
    simpa using (le_div_iff₀ hspos).mp hratio
  exact hd.trans hsle

/-- The relative error `d^(-eta^3)` in the conflict-free theorem. -/
def jmCFMError (delta eta : ℝ) (n : ℕ) : ℝ :=
  (jmDegreeScale delta n) ^ (-(eta ^ 3))

theorem jmCFMError_tendsto_zero {delta eta : ℝ}
    (hdelta : delta < 3) (heta : 0 < eta) :
    Tendsto (jmCFMError delta eta) atTop (nhds 0) := by
  exact (tendsto_rpow_neg_atTop (pow_pos heta 3)).comp
    (jmDegreeScale_tendsto_atTop hdelta)

theorem jmCFMError_eq_base_rpow {delta eta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmCFMError delta eta n =
      (n : ℝ) ^ (-((3 - delta) * eta ^ 3)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold jmCFMError jmDegreeScale
  rw [← Real.rpow_mul hnreal.le]
  congr 1
  ring

theorem jmRho_sq_eq_base_rpow {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    (jmRho delta n) ^ 2 = (n : ℝ) ^ (-(2 * delta)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold jmRho
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnreal.le]
  congr 1
  ring

/-- With the selected hierarchy, the CFM relative error is bounded by the
`n^(-2*delta)` scale used in the leave estimates. -/
theorem jmCFMError_le_rho_sq {eta0 : ℝ} (heta0 : 0 < eta0)
    {n : ℕ} (hn : 0 < n) :
    jmCFMError (jmDelta eta0) (jmEta eta0) n ≤
      (jmRho (jmDelta eta0) n) ^ 2 := by
  rw [jmCFMError_eq_base_rpow hn, jmRho_sq_eq_base_rpow hn]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hn
  · have h := jm_two_delta_lt_degree_exponent heta0
    linarith

/-- The exponential capacity appearing in both the CFM vertex/test-family
bound and the concentration union bounds. -/
def jmExponentialCapacity (delta eta : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((jmDegreeScale delta n) ^ (eta ^ 3))

/-- Every fixed real power of `n` is eventually below the CFM exponential
capacity.  This discharges polynomially many vertices, tests, or bad events. -/
theorem eventually_rpow_le_jmExponentialCapacity
    {delta eta : ℝ} (a : ℝ) (hdelta : delta < 3) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ a ≤ jmExponentialCapacity delta eta n := by
  let b : ℝ := (3 - delta) * eta ^ 3
  have hb : 0 < b := mul_pos (sub_pos.mpr hdelta) (pow_pos heta 3)
  let s : ℝ := a / b
  have hinner : Tendsto (fun n : ℕ =>
      (jmDegreeScale delta n) ^ (eta ^ 3)) atTop atTop :=
    (tendsto_rpow_atTop (pow_pos heta 3)).comp
      (jmDegreeScale_tendsto_atTop hdelta)
  have hraw : ∀ᶠ x : ℝ in atTop, ‖x ^ s‖ ≤ ‖Real.exp x‖ :=
    (isLittleO_rpow_exp_atTop s).eventuallyLE
  have hpulled : ∀ᶠ n : ℕ in atTop,
      ‖((jmDegreeScale delta n) ^ (eta ^ 3)) ^ s‖ ≤
        ‖Real.exp ((jmDegreeScale delta n) ^ (eta ^ 3))‖ :=
    hinner hraw
  filter_upwards [hpulled, eventually_gt_atTop (0 : ℕ)] with n hcap hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hinner_eq : (jmDegreeScale delta n) ^ (eta ^ 3) =
      (n : ℝ) ^ b := by
    unfold jmDegreeScale b
    rw [← Real.rpow_mul hnreal.le]
  have hpower : (n : ℝ) ^ a =
      ((jmDegreeScale delta n) ^ (eta ^ 3)) ^ s := by
    rw [hinner_eq]
    calc
      (n : ℝ) ^ a = (n : ℝ) ^ (b * s) := by
        congr 1
        dsimp [s]
        field_simp [hb.ne']
      _ = ((n : ℝ) ^ b) ^ s := Real.rpow_mul hnreal.le _ _
  have hdeg : 0 ≤ jmDegreeScale delta n := by
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hinside_nonneg : 0 ≤ (jmDegreeScale delta n) ^ (eta ^ 3) :=
    Real.rpow_nonneg hdeg _
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hinside_nonneg _),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hcap
  rw [hpower, jmExponentialCapacity]
  exact hcap

theorem eventually_jmCFMError_le {delta eta epsilon : ℝ}
    (hdelta : delta < 3) (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, jmCFMError delta eta n ≤ epsilon := by
  exact (jmCFMError_tendsto_zero hdelta heta).eventually_le_const hepsilon

/-! ## The local-lemma numerical check -/

/-- After cancelling the `t^2` in `p_bad (D+1)`, the symmetric LLL check is
reduced to this expression (the harmless `+1` in the dependency degree is
absorbed in the constant). -/
def jmLLLFactor (delta : ℝ) (n : ℕ) : ℝ :=
  28 * Real.exp 1 * jmRho delta n

theorem jmLLLFactor_tendsto_zero {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (jmLLLFactor delta) atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 28 * Real.exp 1 * jmRho delta n)
    atTop (nhds 0)
  convert tendsto_const_nhds.mul (jmRho_tendsto_zero hdelta) using 1 <;>
    norm_num

theorem eventually_jmLLLFactor_le_one {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, jmLLLFactor delta n ≤ 1 := by
  exact (jmLLLFactor_tendsto_zero hdelta).eventually_le_const zero_lt_one

/-- The uncancelled symmetric-LLL expression from the completion step:
`e * (2/t^2) * (13 t^2 rho + 1)`. -/
def jmExactLLLExpression (delta : ℝ) (n : ℕ) : ℝ :=
  Real.exp 1 * (2 * (jmFreshColors delta n : ℝ)⁻¹ ^ 2) *
    (13 * (jmFreshColors delta n : ℝ) ^ 2 * jmRho delta n + 1)

theorem jmFreshColors_tendsto_atTop {delta : ℝ} (hdelta : delta < 1) :
    Tendsto (jmFreshColors delta) atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp
    ((tendsto_rpow_atTop (sub_pos.mpr hdelta)).comp
      tendsto_natCast_atTop_atTop)

theorem jmExactLLLExpression_tendsto_zero
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    Tendsto (jmExactLLLExpression delta) atTop (nhds 0) := by
  have htNat := jmFreshColors_tendsto_atTop hdelta1
  have ht : Tendsto (fun n : ℕ => (jmFreshColors delta n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htNat
  have htinv : Tendsto (fun n : ℕ => (jmFreshColors delta n : ℝ)⁻¹)
      atTop (nhds 0) := ht.inv_tendsto_atTop
  have hmodel : Tendsto (fun n : ℕ =>
      2 * Real.exp 1 * (13 * jmRho delta n +
        (jmFreshColors delta n : ℝ)⁻¹ ^ 2)) atTop (nhds 0) := by
    have hscaled : Tendsto (fun n : ℕ => (13 : ℝ) * jmRho delta n)
        atTop (nhds 0) := by
      convert (show Tendsto (fun _ : ℕ => (13 : ℝ)) atTop (nhds 13) from
        tendsto_const_nhds).mul (jmRho_tendsto_zero hdelta0) using 1 <;>
          norm_num
    have hinside : Tendsto (fun n : ℕ =>
        13 * jmRho delta n + (jmFreshColors delta n : ℝ)⁻¹ ^ 2)
        atTop (nhds 0) := by
      convert hscaled.add (htinv.pow 2) using 1 <;> norm_num
    have hout : Tendsto (fun _ : ℕ => (2 * Real.exp 1 : ℝ)) atTop
        (nhds (2 * Real.exp 1)) := tendsto_const_nhds
    convert hout.mul hinside using 1 <;> norm_num
  refine hmodel.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have htpos : 0 < jmFreshColors delta n := by
    apply (Nat.one_le_ceil_iff.mpr ?_)
    unfold jmFreshPaletteReal
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have htne : (jmFreshColors delta n : ℝ) ≠ 0 := by exact_mod_cast htpos.ne'
  unfold jmExactLLLExpression
  field_simp

theorem eventually_jmExactLLLExpression_le_one
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∀ᶠ n : ℕ in atTop, jmExactLLLExpression delta n ≤ 1 := by
  exact (jmExactLLLExpression_tendsto_zero hdelta0 hdelta1).eventually_le_const
    zero_lt_one

/-! ## Literal incidence bound used by `LeaveCompletion` -/

/-- Conservative number of bad events through one leave edge when the
leave-degree and old-cross multiplicity are both bounded by `B` and the
fresh palette has size `t`.  The three contributions are bounded by
`4Bt`, `16B²`, and `8Bt`, respectively. -/
def jmLeaveIncidenceBound (B t : ℕ) : ℕ :=
  12 * B * t + 16 * B ^ 2

/-- The exact expression expected by
`LeaveCompletion.colorable_of_sparse_leave`, after substituting the closed
incidence bound above for its natural parameter `R`. -/
def jmLeaveFourMulExpression (delta : ℝ) (B : ℕ → ℕ) (n : ℕ) : ℝ :=
  4 * (1 / (jmFreshColors delta n : ℝ) ^ 2) *
    (((4 * jmLeaveIncidenceBound (B n) (jmFreshColors delta n) + 1 : ℕ) : ℝ))

theorem jm_leave_scale_div {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (1 - 2 * delta) / (n : ℝ) ^ (1 - delta) =
      jmRho delta n := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply (div_eq_iff (Real.rpow_pos_of_pos hnreal _).ne').2
  unfold jmRho
  calc
    (n : ℝ) ^ (1 - 2 * delta) =
        (n : ℝ) ^ (-delta + (1 - delta)) := by ring_nf
    _ = (n : ℝ) ^ (-delta) * (n : ℝ) ^ (1 - delta) :=
      Real.rpow_add hnreal _ _

/-- A leave/cross bound of order `n^(1-2delta)` is negligible compared with
the fresh palette `ceil(n^(1-delta))`. -/
theorem jm_leave_ratio_tendsto_zero
    (B : ℕ → ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (hB : ∀ᶠ n : ℕ in atTop,
      (B n : ℝ) ≤ (n : ℝ) ^ (1 - 2 * delta)) :
    Tendsto (fun n : ℕ => (B n : ℝ) / (jmFreshColors delta n : ℝ))
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    (jmRho_tendsto_zero hdelta)
  · exact Filter.Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)
  · filter_upwards [hB, eventually_gt_atTop (0 : ℕ)] with n hBn hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hfreshpos : 0 < jmFreshPaletteReal delta n := by
      unfold jmFreshPaletteReal
      exact Real.rpow_pos_of_pos hnreal _
    have ht : jmFreshPaletteReal delta n ≤ (jmFreshColors delta n : ℝ) :=
      jmFreshPaletteReal_le_colors delta n
    have htpos : (0 : ℝ) < (jmFreshColors delta n : ℝ) :=
      hfreshpos.trans_le ht
    calc
      (B n : ℝ) / (jmFreshColors delta n : ℝ) ≤
          (n : ℝ) ^ (1 - 2 * delta) /
            (jmFreshColors delta n : ℝ) :=
        div_le_div_of_nonneg_right hBn (Nat.cast_nonneg _)
      _ ≤ (n : ℝ) ^ (1 - 2 * delta) /
          jmFreshPaletteReal delta n := by
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
          hfreshpos ht
      _ = jmRho delta n := by
        unfold jmFreshPaletteReal
        exact jm_leave_scale_div hn

/-- Affine-envelope version used after natural-number rounding.  Fixed
constant factors and additive rounding errors do not change `B / t → 0`. -/
theorem jm_leave_ratio_tendsto_zero_of_affine_bound
    (B : ℕ → ℕ) {delta C C0 : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hB : ∀ᶠ n : ℕ in atTop,
      (B n : ℝ) ≤ C * (n : ℝ) ^ (1 - 2 * delta) + C0) :
    Tendsto (fun n : ℕ => (B n : ℝ) / (jmFreshColors delta n : ℝ))
      atTop (nhds 0) := by
  have hfreshTop : Tendsto (jmFreshPaletteReal delta) atTop atTop := by
    exact (tendsto_rpow_atTop (sub_pos.mpr hdelta1)).comp
      tendsto_natCast_atTop_atTop
  have hfreshInv : Tendsto (fun n : ℕ => (jmFreshPaletteReal delta n)⁻¹)
      atTop (nhds 0) := hfreshTop.inv_tendsto_atTop
  have hupper : Tendsto (fun n : ℕ =>
      C * jmRho delta n + C0 * (jmFreshPaletteReal delta n)⁻¹)
      atTop (nhds 0) := by
    have h₁ : Tendsto (fun n : ℕ => C * jmRho delta n) atTop (nhds 0) := by
      convert (show Tendsto (fun _ : ℕ => C) atTop (nhds C) from
        tendsto_const_nhds).mul (jmRho_tendsto_zero hdelta0) using 1 <;>
          norm_num
    have h₂ : Tendsto (fun n : ℕ =>
        C0 * (jmFreshPaletteReal delta n)⁻¹) atTop (nhds 0) := by
      convert (show Tendsto (fun _ : ℕ => C0) atTop (nhds C0) from
        tendsto_const_nhds).mul hfreshInv using 1 <;> norm_num
    convert h₁.add h₂ using 1 <;> norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hupper
  · exact Filter.Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)
  · filter_upwards [hB, eventually_gt_atTop (0 : ℕ)] with n hBn hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hscale : 0 ≤ (n : ℝ) ^ (1 - 2 * delta) :=
      Real.rpow_nonneg hnreal.le _
    have henv : 0 ≤ C * (n : ℝ) ^ (1 - 2 * delta) + C0 :=
      add_nonneg (mul_nonneg hC hscale) hC0
    have hfreshpos : 0 < jmFreshPaletteReal delta n := by
      unfold jmFreshPaletteReal
      exact Real.rpow_pos_of_pos hnreal _
    have ht : jmFreshPaletteReal delta n ≤ (jmFreshColors delta n : ℝ) :=
      jmFreshPaletteReal_le_colors delta n
    calc
      (B n : ℝ) / (jmFreshColors delta n : ℝ) ≤
          (C * (n : ℝ) ^ (1 - 2 * delta) + C0) /
            (jmFreshColors delta n : ℝ) :=
        div_le_div_of_nonneg_right hBn (Nat.cast_nonneg _)
      _ ≤ (C * (n : ℝ) ^ (1 - 2 * delta) + C0) /
          jmFreshPaletteReal delta n := by
        exact div_le_div_of_nonneg_left henv hfreshpos ht
      _ = C * jmRho delta n +
          C0 * (jmFreshPaletteReal delta n)⁻¹ := by
        have hs : (n : ℝ) ^ (1 - 2 * delta) *
            (jmFreshPaletteReal delta n)⁻¹ = jmRho delta n := by
          simpa only [jmFreshPaletteReal, div_eq_mul_inv] using
            (jm_leave_scale_div (delta := delta) hn)
        rw [add_div, mul_div_assoc]
        simp only [div_eq_mul_inv]
        rw [hs]

theorem jmLeaveFourMulExpression_eq
    (B : ℕ → ℕ) {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmLeaveFourMulExpression delta B n =
      192 * ((B n : ℝ) / (jmFreshColors delta n : ℝ)) +
      256 * ((B n : ℝ) / (jmFreshColors delta n : ℝ)) ^ 2 +
      4 * (jmFreshColors delta n : ℝ)⁻¹ ^ 2 := by
  have htpos : 0 < jmFreshColors delta n := by
    apply (Nat.one_le_ceil_iff.mpr ?_)
    unfold jmFreshPaletteReal
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have htne : (jmFreshColors delta n : ℝ) ≠ 0 := by exact_mod_cast htpos.ne'
  unfold jmLeaveFourMulExpression jmLeaveIncidenceBound
  push_cast
  field_simp
  ring

/-- The exact ceiling-aware local-lemma multiplier required by
`LeaveCompletion.colorable_of_sparse_leave` tends to zero. -/
theorem jmLeaveFourMulExpression_tendsto_zero
    (B : ℕ → ℕ) {delta : ℝ} (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hB : ∀ᶠ n : ℕ in atTop,
      (B n : ℝ) ≤ (n : ℝ) ^ (1 - 2 * delta)) :
    Tendsto (jmLeaveFourMulExpression delta B) atTop (nhds 0) := by
  have hdelta1 : delta < 1 := hdeltaHalf.trans (by norm_num)
  have hratio := jm_leave_ratio_tendsto_zero B hdelta0 hB
  have htNat := jmFreshColors_tendsto_atTop hdelta1
  have ht : Tendsto (fun n : ℕ => (jmFreshColors delta n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htNat
  have htinv : Tendsto (fun n : ℕ => (jmFreshColors delta n : ℝ)⁻¹)
      atTop (nhds 0) := ht.inv_tendsto_atTop
  have hterm1 : Tendsto (fun n : ℕ =>
      (192 : ℝ) * ((B n : ℝ) / (jmFreshColors delta n : ℝ)))
      atTop (nhds 0) := by
    convert (show Tendsto (fun _ : ℕ => (192 : ℝ)) atTop (nhds 192) from
      tendsto_const_nhds).mul hratio using 1 <;> norm_num
  have hterm2 : Tendsto (fun n : ℕ =>
      (256 : ℝ) * ((B n : ℝ) / (jmFreshColors delta n : ℝ)) ^ 2)
      atTop (nhds 0) := by
    convert (show Tendsto (fun _ : ℕ => (256 : ℝ)) atTop (nhds 256) from
      tendsto_const_nhds).mul (hratio.pow 2) using 1 <;> norm_num
  have hterm3 : Tendsto (fun n : ℕ =>
      (4 : ℝ) * (jmFreshColors delta n : ℝ)⁻¹ ^ 2)
      atTop (nhds 0) := by
    convert (show Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4) from
      tendsto_const_nhds).mul (htinv.pow 2) using 1 <;> norm_num
  have hmodel : Tendsto (fun n : ℕ =>
      192 * ((B n : ℝ) / (jmFreshColors delta n : ℝ)) +
      256 * ((B n : ℝ) / (jmFreshColors delta n : ℝ)) ^ 2 +
      4 * (jmFreshColors delta n : ℝ)⁻¹ ^ 2) atTop (nhds 0) := by
    convert (hterm1.add hterm2).add hterm3 using 1 <;> norm_num
  refine hmodel.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (jmLeaveFourMulExpression_eq B hn).symm

/-- Literal eventual hypothesis for the compiled sparse-leave completion
theorem.  No comparison of proxy constants is required at the call site. -/
theorem eventually_jmLeave_four_mul_le_one
    (B : ℕ → ℕ) {delta : ℝ} (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hB : ∀ᶠ n : ℕ in atTop,
      (B n : ℝ) ≤ (n : ℝ) ^ (1 - 2 * delta)) :
    ∀ᶠ n : ℕ in atTop,
      4 * (1 / (jmFreshColors delta n : ℝ) ^ 2) *
        (((4 * jmLeaveIncidenceBound (B n) (jmFreshColors delta n) + 1 : ℕ) : ℝ)) ≤
          1 := by
  exact (jmLeaveFourMulExpression_tendsto_zero B hdelta0 hdeltaHalf hB).eventually_le_const
    zero_lt_one

/-- Affine-envelope version of the exact completion multiplier.  This is
the integration theorem for a natural leave bound obtained after fixed
constants and ceiling errors. -/
theorem jmLeaveFourMulExpression_tendsto_zero_of_affine_bound
    (B : ℕ → ℕ) {delta C C0 : ℝ}
    (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hB : ∀ᶠ n : ℕ in atTop,
      (B n : ℝ) ≤ C * (n : ℝ) ^ (1 - 2 * delta) + C0) :
    Tendsto (jmLeaveFourMulExpression delta B) atTop (nhds 0) := by
  have hdelta1 : delta < 1 := hdeltaHalf.trans (by norm_num)
  have hratio := jm_leave_ratio_tendsto_zero_of_affine_bound
    B hdelta0 hdelta1 hC hC0 hB
  have htNat := jmFreshColors_tendsto_atTop hdelta1
  have ht : Tendsto (fun n : ℕ => (jmFreshColors delta n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htNat
  have htinv : Tendsto (fun n : ℕ => (jmFreshColors delta n : ℝ)⁻¹)
      atTop (nhds 0) := ht.inv_tendsto_atTop
  have hterm1 : Tendsto (fun n : ℕ =>
      (192 : ℝ) * ((B n : ℝ) / (jmFreshColors delta n : ℝ)))
      atTop (nhds 0) := by
    convert (show Tendsto (fun _ : ℕ => (192 : ℝ)) atTop (nhds 192) from
      tendsto_const_nhds).mul hratio using 1 <;> norm_num
  have hterm2 : Tendsto (fun n : ℕ =>
      (256 : ℝ) * ((B n : ℝ) / (jmFreshColors delta n : ℝ)) ^ 2)
      atTop (nhds 0) := by
    convert (show Tendsto (fun _ : ℕ => (256 : ℝ)) atTop (nhds 256) from
      tendsto_const_nhds).mul (hratio.pow 2) using 1 <;> norm_num
  have hterm3 : Tendsto (fun n : ℕ =>
      (4 : ℝ) * (jmFreshColors delta n : ℝ)⁻¹ ^ 2)
      atTop (nhds 0) := by
    convert (show Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4) from
      tendsto_const_nhds).mul (htinv.pow 2) using 1 <;> norm_num
  have hmodel : Tendsto (fun n : ℕ =>
      192 * ((B n : ℝ) / (jmFreshColors delta n : ℝ)) +
      256 * ((B n : ℝ) / (jmFreshColors delta n : ℝ)) ^ 2 +
      4 * (jmFreshColors delta n : ℝ)⁻¹ ^ 2) atTop (nhds 0) := by
    convert (hterm1.add hterm2).add hterm3 using 1 <;> norm_num
  refine hmodel.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (jmLeaveFourMulExpression_eq B hn).symm

/-- Exact eventual hypothesis for `colorable_of_sparse_leave`, allowing a
fixed constant multiple and an additive natural-rounding error. -/
theorem eventually_jmLeave_four_mul_le_one_of_affine_bound
    (B : ℕ → ℕ) {delta C C0 : ℝ}
    (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hB : ∀ᶠ n : ℕ in atTop,
      (B n : ℝ) ≤ C * (n : ℝ) ^ (1 - 2 * delta) + C0) :
    ∀ᶠ n : ℕ in atTop,
      4 * (1 / (jmFreshColors delta n : ℝ) ^ 2) *
        (((4 * jmLeaveIncidenceBound (B n) (jmFreshColors delta n) + 1 : ℕ) : ℝ)) ≤
          1 := by
  exact (jmLeaveFourMulExpression_tendsto_zero_of_affine_bound
    B hdelta0 hdeltaHalf hC hC0 hB).eventually_le_const zero_lt_one

/-- Canonical natural leave bound used by the tracked construction. -/
def jmCeilLeaveBound (C C0 delta : ℝ) (n : ℕ) : ℕ :=
  ⌈C * (n : ℝ) ^ (1 - 2 * delta) + C0⌉₊

theorem jmCeilLeaveBound_cast_le
    {C C0 delta : ℝ} (hC : 0 ≤ C) (hC0 : 0 ≤ C0) (n : ℕ) :
    (jmCeilLeaveBound C C0 delta n : ℝ) ≤
      C * (n : ℝ) ^ (1 - 2 * delta) + C0 + 1 := by
  unfold jmCeilLeaveBound
  exact (Nat.ceil_lt_add_one
    (add_nonneg (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hC0)).le

/-- Ready-to-use ceiling specialization; its conclusion is literally the
real inequality consumed by `LeaveCompletion.colorable_of_sparse_leave`. -/
theorem eventually_jmCeilLeaveBound_four_mul_le_one
    {delta C C0 : ℝ}
    (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hC : 0 ≤ C) (hC0 : 0 ≤ C0) :
    ∀ᶠ n : ℕ in atTop,
      4 * (1 / (jmFreshColors delta n : ℝ) ^ 2) *
        (((4 * jmLeaveIncidenceBound (jmCeilLeaveBound C C0 delta n)
          (jmFreshColors delta n) + 1 : ℕ) : ℝ)) ≤ 1 := by
  apply eventually_jmLeave_four_mul_le_one_of_affine_bound
    (jmCeilLeaveBound C C0 delta) hdelta0 hdeltaHalf hC
    (add_nonneg hC0 zero_le_one)
  exact Filter.Eventually.of_forall fun n => by
    have h := jmCeilLeaveBound_cast_le (delta := delta) hC hC0 n
    simpa [add_assoc] using h

/-! ## Arithmetic package for the selected auxiliary degree -/

/-- A fixed constant times a smaller real power of `n` is eventually below
a larger real power.  Keeping this elementary bridge here avoids repeating
the same limit argument in every CFM numerical check. -/
theorem eventually_const_mul_rpow_le_rpow
    {C a b : ℝ} (hC : 0 ≤ C) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have htop : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [htop (eventually_ge_atTop C),
    eventually_ge_atTop (1 : ℕ)] with n hnC hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn)
  calc
    C * (n : ℝ) ^ a ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hnC (Real.rpow_nonneg hnreal.le _)
    _ = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnreal]
      congr 1
      ring

/-- The exact auxiliary degree is nonnegative, including at `n = 0`. -/
theorem jmAuxDegreeReal_nonneg (delta : ℝ) (n : ℕ) :
    0 ≤ jmAuxDegreeReal delta n := by
  have hrho : 0 ≤ jmRho delta n :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hp : 0 ≤ jmRetention delta n := by
    unfold jmRetention
    exact div_nonneg hrho (by linarith)
  have hq : 0 ≤ jmDeletion delta n := by
    unfold jmDeletion
    exact div_nonneg zero_le_one (by linarith)
  unfold jmAuxDegreeReal
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (n : ℝ)))
        (jmOldPaletteReal_nonneg delta n))
      (pow_nonneg hq 4))
    hp

/-- Eventually the asymptotic degree scale is bounded by the exact central
degree.  This is the useful monotone form of `jmAuxDegreeReal_ratio_tendsto`. -/
theorem eventually_jmDegreeScale_le_auxDegree {delta : ℝ}
    (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      jmDegreeScale delta n ≤ jmAuxDegreeReal delta n := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ jmAuxDegreeReal delta n / jmDegreeScale delta n :=
    (jmAuxDegreeReal_ratio_tendsto hdelta).eventually_const_le (by norm_num)
  filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)] with n hratio hn
  have hspos : 0 < jmDegreeScale delta n := by
    unfold jmDegreeScale
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  simpa using (le_div_iff₀ hspos).mp hratio

/-- The old palette has at most `n` colours for all sufficiently large `n`.
This is the ceiling-aware form needed to replace the palette parameter `k`
by `n` in the common-link count. -/
theorem eventually_jmOldColors_le {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, jmOldColors delta n ≤ n := by
  have hrho : ∀ᶠ n : ℕ in atTop, jmRho delta n ≤ (1 / 10 : ℝ) :=
    (jmRho_tendsto_zero hdelta).eventually_le_const (by norm_num)
  filter_upwards [hrho, eventually_ge_atTop (12 : ℕ)] with n hrho hn
  have hnreal : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnrho : (n : ℝ) * jmRho delta n ≤ (n : ℝ) * (1 / 10 : ℝ) :=
    mul_le_mul_of_nonneg_left hrho (by positivity)
  have hceil := jmOldColors_lt_add_one delta n
  have hreal : (jmOldColors delta n : ℝ) ≤ (n : ℝ) := by
    apply le_of_lt
    calc
      (jmOldColors delta n : ℝ) < jmOldPaletteReal delta n + 1 := hceil
      _ ≤ (n : ℝ) := by
        unfold jmOldPaletteReal
        nlinarith
  exact_mod_cast hreal

/-- Generic polynomial comparison with a positive power of the exact
auxiliary degree. -/
theorem eventually_const_mul_rpow_le_auxDegree_rpow
    {eta0 C a b : ℝ} (heta0 : 0 < eta0) (hC : 0 ≤ C) (hb : 0 < b)
    (hgap : a < (3 - jmDelta eta0) * b) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ a ≤
        (jmAuxDegreeReal (jmDelta eta0) n) ^ b := by
  have hdelta := jmDelta_pos heta0
  filter_upwards [eventually_const_mul_rpow_le_rpow hC hgap,
    eventually_jmDegreeScale_le_auxDegree hdelta,
    eventually_gt_atTop (0 : ℕ)] with n hpoly hscale hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hscale_nonneg : 0 ≤ jmDegreeScale (jmDelta eta0) n :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc
    C * (n : ℝ) ^ a ≤
        (n : ℝ) ^ ((3 - jmDelta eta0) * b) := hpoly
    _ = (jmDegreeScale (jmDelta eta0) n) ^ b := by
      unfold jmDegreeScale
      exact Real.rpow_mul hnreal.le _ _
    _ ≤ (jmAuxDegreeReal (jmDelta eta0) n) ^ b :=
      Real.rpow_le_rpow hscale_nonneg hscale hb.le

/-- The exponent gap behind the concrete `566231040 n^8` W3 threshold. -/
theorem jm_eight_lt_degree_three_sub_eta {eta0 : ℝ} (heta0 : 0 < eta0) :
    (8 : ℝ) <
      (3 - jmDelta eta0) * (3 - jmEta eta0) := by
  have hd0 := (jmDelta_pos heta0).le
  have hd := jmDelta_le_one_ten_thousandth eta0
  have he0 := (jmEta_pos heta0).le
  have he : jmEta eta0 ≤ (1 / 100 : ℝ) := min_le_right _ _
  nlinarith [mul_nonneg hd0 he0]

/-- Literal W3 threshold consumed by `TrackedTests` and `ConflictCounts`. -/
theorem eventually_jm_commonLink_n8_le_auxDegree {eta0 : ℝ}
    (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop,
      ((566231040 * n ^ 8 : ℕ) : ℝ) ≤
        (jmAuxDegreeReal (jmDelta eta0) n) ^ (3 - jmEta eta0) := by
  have hb : 0 < 3 - jmEta eta0 := by
    have := jmEta_lt_one heta0
    linarith
  have h := eventually_const_mul_rpow_le_auxDegree_rpow
    heta0 (C := (566231040 : ℝ)) (a := 8) (b := 3 - jmEta eta0)
    (by norm_num) hb (jm_eight_lt_degree_three_sub_eta heta0)
  filter_upwards [h] with n hn
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simpa [Real.rpow_natCast] using hn

/-- The exponent gap used for the ambient auxiliary-hypergraph pair
codegree.  This is deliberately separate from the smaller same-colour
paint-fibre scale: an arbitrary active auxiliary pair can have order `n^2`
extensions, but that is still far below `d^(1-eta)` when `d` has order
`n^(3-delta)`. -/
theorem jm_two_lt_degree_one_sub_eta {eta0 : ℝ} (heta0 : 0 < eta0) :
    (2 : ℝ) <
      (3 - jmDelta eta0) * (1 - jmEta eta0) := by
  have hd0 := (jmDelta_pos heta0).le
  have hd := jmDelta_le_one_ten_thousandth eta0
  have he0 := (jmEta_pos heta0).le
  have he : jmEta eta0 ≤ (1 / 100 : ℝ) := min_le_right _ _
  nlinarith [mul_nonneg hd0 he0]

/-- Any fixed constant times `n^2` is eventually below the ambient host
codegree threshold.  Consumers should use this for `MaxCodegreeLE`; the
ceiling bound `jmPairCodegreeCeil` remains the sharper paint-fibre input to
the conflict-count estimates. -/
theorem eventually_const_mul_n_sq_le_auxDegree_one_sub_eta
    {eta0 C : ℝ} (heta0 : 0 < eta0) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ (2 : ℝ) ≤
        (jmAuxDegreeReal (jmDelta eta0) n) ^ (1 - jmEta eta0) := by
  have hb : 0 < 1 - jmEta eta0 := by
    have := jmEta_lt_one heta0
    linarith
  exact eventually_const_mul_rpow_le_auxDegree_rpow
    heta0 hC hb (jm_two_lt_degree_one_sub_eta heta0)

/-- Natural-number form of the ambient pair-codegree comparison. -/
theorem eventually_nat_const_mul_sq_le_auxDegree_one_sub_eta
    (C : ℕ) {eta0 : ℝ} (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop,
      ((C * n ^ 2 : ℕ) : ℝ) ≤
        (jmAuxDegreeReal (jmDelta eta0) n) ^ (1 - jmEta eta0) := by
  have h := eventually_const_mul_n_sq_le_auxDegree_one_sub_eta
    (eta0 := eta0) (C := (C : ℝ)) heta0 (Nat.cast_nonneg C)
  filter_upwards [h] with n hn
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simpa [Real.rpow_natCast] using hn

/-- The actual CFM error based on the exact degree is no larger than the
bookkeeping error based on `jmDegreeScale`. -/
theorem eventually_auxDegree_cfmError_le_jmCFMError {eta0 : ℝ}
    (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop,
      (jmAuxDegreeReal (jmDelta eta0) n) ^ (-(jmEta eta0) ^ 3) ≤
        jmCFMError (jmDelta eta0) (jmEta eta0) n := by
  filter_upwards [eventually_jmDegreeScale_le_auxDegree (jmDelta_pos heta0),
    eventually_gt_atTop (0 : ℕ)] with n hscale hn
  have hspos : 0 < jmDegreeScale (jmDelta eta0) n := by
    unfold jmDegreeScale
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hdpos : 0 < jmAuxDegreeReal (jmDelta eta0) n := hspos.trans_le hscale
  rw [Real.rpow_neg hdpos.le, jmCFMError, Real.rpow_neg hspos.le]
  simpa [one_div] using one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos hspos (jmEta eta0 ^ 3))
    (Real.rpow_le_rpow hspos.le hscale (pow_nonneg (jmEta_pos heta0).le 3))

/-- Consequently the actual CFM error is also at most `rho^2`. -/
theorem eventually_auxDegree_cfmError_le_rho_sq {eta0 : ℝ}
    (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop,
      (jmAuxDegreeReal (jmDelta eta0) n) ^ (-(jmEta eta0) ^ 3) ≤
        (jmRho (jmDelta eta0) n) ^ 2 := by
  filter_upwards [eventually_auxDegree_cfmError_le_jmCFMError heta0,
    eventually_gt_atTop (0 : ℕ)] with n haux hn
  exact haux.trans (jmCFMError_le_rho_sq heta0 hn)

/-- Fixed coefficients can be absorbed into the exponential capacity. -/
theorem eventually_const_mul_rpow_le_jmExponentialCapacity
    {delta eta C a : ℝ} (hdelta : delta < 3) (heta : 0 < eta)
    (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ a ≤ jmExponentialCapacity delta eta n := by
  have hnatCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hcast : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hnatCast (eventually_ge_atTop C)
  filter_upwards [eventually_rpow_le_jmExponentialCapacity
      (a + 1) hdelta heta,
    eventually_ge_atTop (1 : ℕ),
    hcast] with n hcapacity hn hnC
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn)
  calc
    C * (n : ℝ) ^ a ≤ (n : ℝ) * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hnC (Real.rpow_nonneg hnreal.le _)
    _ = (n : ℝ) ^ (a + 1) := by
      rw [add_comm, Real.rpow_add hnreal, Real.rpow_one]
    _ ≤ jmExponentialCapacity delta eta n := hcapacity

/-- The scale-based exponential capacity is eventually bounded by the one
formed from the exact auxiliary degree. -/
theorem eventually_jmExponentialCapacity_le_auxDegree {eta0 : ℝ}
    (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop,
      jmExponentialCapacity (jmDelta eta0) (jmEta eta0) n ≤
        Real.exp ((jmAuxDegreeReal (jmDelta eta0) n) ^
          ((jmEta eta0) ^ 3)) := by
  filter_upwards [eventually_jmDegreeScale_le_auxDegree (jmDelta_pos heta0)]
      with n hscale
  unfold jmExponentialCapacity
  apply Real.exp_le_exp.mpr
  exact Real.rpow_le_rpow
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hscale
    (pow_nonneg (jmEta_pos heta0).le 3)

/-- Any explicitly polynomially bounded natural family (in particular the
active vertices or the finite test index) fits the CFM exponential cutoff. -/
theorem eventually_natPolynomial_le_auxDegree_exponential
    {eta0 C a : ℝ} (P : ℕ → ℕ) (heta0 : 0 < eta0) (hC : 0 ≤ C)
    (hP : ∀ᶠ n : ℕ in atTop, (P n : ℝ) ≤ C * (n : ℝ) ^ a) :
    ∀ᶠ n : ℕ in atTop,
      (P n : ℝ) ≤ Real.exp ((jmAuxDegreeReal (jmDelta eta0) n) ^
        ((jmEta eta0) ^ 3)) := by
  have hd3 : jmDelta eta0 < 3 :=
    (jmDelta_lt_one heta0).trans (by norm_num)
  filter_upwards [hP,
    eventually_const_mul_rpow_le_jmExponentialCapacity hd3
      (jmEta_pos heta0) hC,
    eventually_jmExponentialCapacity_le_auxDegree heta0]
      with n hP hcap haux
  exact hP.trans (hcap.trans haux)

/-- The ambient active-vertex bound `(n+1 choose 2) + nk`, with the selected
old palette substituted for `k`, satisfies the CFM exponential cutoff. -/
theorem eventually_jmActiveVertexPolynomial_le_auxDegree_exponential
    {eta0 : ℝ} (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop,
      (((n + 1).choose 2 + n * jmOldColors (jmDelta eta0) n : ℕ) : ℝ) ≤
        Real.exp ((jmAuxDegreeReal (jmDelta eta0) n) ^
          ((jmEta eta0) ^ 3)) := by
  let P : ℕ → ℕ := fun n =>
    (n + 1).choose 2 + n * jmOldColors (jmDelta eta0) n
  have hP : ∀ᶠ n : ℕ in atTop, (P n : ℝ) ≤ 5 * (n : ℝ) ^ (2 : ℝ) := by
    filter_upwards [eventually_jmOldColors_le (jmDelta_pos heta0),
      eventually_ge_atTop (1 : ℕ)] with n hk hn
    have hchoose : (n + 1).choose 2 ≤ (n + 1) ^ 2 :=
      Nat.choose_le_pow _ _
    have hnat : P n ≤ 5 * n ^ 2 := by
      dsimp [P]
      calc
        (n + 1).choose 2 + n * jmOldColors (jmDelta eta0) n ≤
            (n + 1) ^ 2 + n * n := Nat.add_le_add hchoose (Nat.mul_le_mul_left n hk)
        _ ≤ 5 * n ^ 2 := by nlinarith
    exact_mod_cast hnat
  simpa [P] using eventually_natPolynomial_le_auxDegree_exponential
    P heta0 (C := (5 : ℝ)) (a := 2) (by norm_num) hP

/-- Natural pair-codegree ceiling allowing a fixed additive rounding term. -/
def jmPairCodegreeCeil (C C0 delta : ℝ) (n : ℕ) : ℕ :=
  ⌈C * (n : ℝ) ^ (2 - delta) + C0⌉₊

/-- The additive term in the natural ceiling is eventually absorbed into
the same `n^(2-delta)` scale. -/
theorem eventually_jmPairCodegreeCeil_cast_le
    {C C0 delta : ℝ} (hC : 0 ≤ C) (hC0 : 0 ≤ C0) (hdelta : delta < 2) :
    ∀ᶠ n : ℕ in atTop,
      (jmPairCodegreeCeil C C0 delta n : ℝ) ≤
        (C + C0 + 1) * (n : ℝ) ^ (2 - delta) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (2 - delta) :=
    Real.one_le_rpow hnreal (sub_nonneg.mpr hdelta.le)
  have harg : 0 ≤ C * (n : ℝ) ^ (2 - delta) + C0 :=
    add_nonneg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _)) hC0
  have hceil : (jmPairCodegreeCeil C C0 delta n : ℝ) <
      C * (n : ℝ) ^ (2 - delta) + C0 + 1 := by
    exact Nat.ceil_lt_add_one harg
  apply hceil.le.trans
  nlinarith [mul_nonneg (add_nonneg hC (add_nonneg hC0 zero_le_one))
    (sub_nonneg.mpr hpow)]

/-- The common exponent slack in the pair- and triple-conflict codegree
comparisons. -/
theorem jm_conflict_codegree_exponent_gaps {eta0 : ℝ} (heta0 : 0 < eta0) :
    5 - 2 * jmDelta eta0 <
        (3 - jmDelta eta0) * (2 - jmEta eta0) ∧
      2 - jmDelta eta0 <
        (3 - jmDelta eta0) * (1 - jmEta eta0) := by
  have hd0 := (jmDelta_pos heta0).le
  have he0 := (jmEta_pos heta0).le
  have he : jmEta eta0 ≤ (1 / 100 : ℝ) := min_le_right _ _
  constructor <;> nlinarith [mul_nonneg hd0 he0]

/-- Degree-layer comparison required by
`alternatingCycleConflicts_isBounded_of_maxCodegree`.  The sole fixed
constant requirement is explicit: the chosen conflict-size cutoff `ell`
must absorb the coefficient `512 C_L^3`. -/
theorem eventually_jmConflict_degree_comparison
    (L : ℕ → ℕ) {eta0 C_L : ℝ} (ell : ℕ)
    (heta0 : 0 < eta0) (hCL : 0 ≤ C_L)
    (hconstant : 512 * C_L ^ 3 ≤ (ell : ℝ))
    (hL : ∀ᶠ n : ℕ in atTop,
      (L n : ℝ) ≤ C_L * (n : ℝ) ^ (2 - jmDelta eta0)) :
    ∀ᶠ n : ℕ in atTop,
      ((512 * n * n * jmOldColors (jmDelta eta0) n *
        L n * L n * L n : ℕ) : ℝ) ≤
        (ell : ℝ) * Real.rpow (jmAuxDegreeReal (jmDelta eta0) n) 3 := by
  filter_upwards [hL,
    eventually_jmOldColors_le (jmDelta_pos heta0),
    eventually_jmDegreeScale_le_auxDegree (jmDelta_pos heta0),
    eventually_gt_atTop (0 : ℕ)] with n hL hk hscale hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkreal : (jmOldColors (jmDelta eta0) n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hk
  have hL0 : 0 ≤ (L n : ℝ) := Nat.cast_nonneg _
  have hscale0 : 0 ≤ jmDegreeScale (jmDelta eta0) n :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hd0 : 0 ≤ jmAuxDegreeReal (jmDelta eta0) n :=
    hscale0.trans hscale
  have hscale_eq :
      (n : ℝ) * (n : ℝ) ^ (2 - jmDelta eta0) =
        jmDegreeScale (jmDelta eta0) n := by
    unfold jmDegreeScale
    calc
      (n : ℝ) * (n : ℝ) ^ (2 - jmDelta eta0) =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (2 - jmDelta eta0) := by
            rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (2 - jmDelta eta0)) := by
            rw [Real.rpow_add hnreal]
      _ = (n : ℝ) ^ (3 - jmDelta eta0) := by ring_nf
  have hnL : (n : ℝ) * (L n : ℝ) ≤
      C_L * jmDegreeScale (jmDelta eta0) n := by
    calc
      (n : ℝ) * (L n : ℝ) ≤
          (n : ℝ) * (C_L * (n : ℝ) ^ (2 - jmDelta eta0)) :=
        mul_le_mul_of_nonneg_left hL hnreal.le
      _ = C_L * jmDegreeScale (jmDelta eta0) n := by
        rw [← hscale_eq]
        ring
  push_cast
  change (512 : ℝ) * n * n * jmOldColors (jmDelta eta0) n *
      L n * L n * L n ≤
    (ell : ℝ) * Real.rpow (jmAuxDegreeReal (jmDelta eta0) n) 3
  calc
    (512 : ℝ) * n * n * jmOldColors (jmDelta eta0) n * L n * L n * L n ≤
        512 * n * n * n * L n * L n * L n := by gcongr
    _ = 512 * ((n : ℝ) * (L n : ℝ)) ^ 3 := by ring
    _ ≤ 512 * (C_L * jmDegreeScale (jmDelta eta0) n) ^ 3 := by
      gcongr
    _ = (512 * C_L ^ 3) * (jmDegreeScale (jmDelta eta0) n) ^ 3 := by ring
    _ ≤ (ell : ℝ) * (jmDegreeScale (jmDelta eta0) n) ^ 3 := by gcongr
    _ ≤ (ell : ℝ) * (jmAuxDegreeReal (jmDelta eta0) n) ^ 3 := by gcongr
    _ = (ell : ℝ) * Real.rpow (jmAuxDegreeReal (jmDelta eta0) n) 3 := by
      norm_num [Real.rpow_natCast]

/-- Pair-codegree comparison required by the concrete conflict-count
adapter. -/
theorem eventually_jmConflict_pair_comparison
    (L : ℕ → ℕ) {eta0 C_L : ℝ} (heta0 : 0 < eta0) (hCL : 0 ≤ C_L)
    (hL : ∀ᶠ n : ℕ in atTop,
      (L n : ℝ) ≤ C_L * (n : ℝ) ^ (2 - jmDelta eta0)) :
    ∀ᶠ n : ℕ in atTop,
      ((3 * 512 * 512 * (n + jmOldColors (jmDelta eta0) n) *
        L n * L n : ℕ) : ℝ) ≤
        (jmAuxDegreeReal (jmDelta eta0) n) ^ (2 - jmEta eta0) := by
  have hgap := (jm_conflict_codegree_exponent_gaps heta0).1
  have hb : 0 < 2 - jmEta eta0 := by linarith [jmEta_lt_one heta0]
  have hgrowth := eventually_const_mul_rpow_le_auxDegree_rpow heta0
    (C := 6 * 512 * 512 * C_L ^ 2)
    (a := 5 - 2 * jmDelta eta0) (b := 2 - jmEta eta0)
    (by positivity) hb hgap
  filter_upwards [hL, eventually_jmOldColors_le (jmDelta_pos heta0),
    hgrowth, eventually_gt_atTop (0 : ℕ)] with n hL hk hgrowth hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkreal : (jmOldColors (jmDelta eta0) n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hk
  have hsum : (n : ℝ) + jmOldColors (jmDelta eta0) n ≤ 2 * n := by linarith
  have henv0 : 0 ≤ C_L * (n : ℝ) ^ (2 - jmDelta eta0) :=
    mul_nonneg hCL (Real.rpow_nonneg hnreal.le _)
  have hpower :
      (n : ℝ) * ((n : ℝ) ^ (2 - jmDelta eta0) *
        (n : ℝ) ^ (2 - jmDelta eta0)) =
        (n : ℝ) ^ (5 - 2 * jmDelta eta0) := by
    calc
      (n : ℝ) * ((n : ℝ) ^ (2 - jmDelta eta0) *
          (n : ℝ) ^ (2 - jmDelta eta0)) =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (2 - jmDelta eta0) *
            (n : ℝ) ^ (2 - jmDelta eta0) := by
              rw [Real.rpow_one]
              ring
      _ = (n : ℝ) ^ ((1 : ℝ) + (2 - jmDelta eta0)) *
            (n : ℝ) ^ (2 - jmDelta eta0) := by
              rw [← Real.rpow_add hnreal]
      _ = (n : ℝ) ^ (((1 : ℝ) + (2 - jmDelta eta0)) +
            (2 - jmDelta eta0)) := by rw [← Real.rpow_add hnreal]
      _ = (n : ℝ) ^ (5 - 2 * jmDelta eta0) := by ring_nf
  push_cast
  change (786432 : ℝ) *
      ((n : ℝ) + jmOldColors (jmDelta eta0) n) * L n * L n ≤
    (jmAuxDegreeReal (jmDelta eta0) n) ^ (2 - jmEta eta0)
  calc
    (786432 : ℝ) * (n + jmOldColors (jmDelta eta0) n) * L n * L n ≤
        786432 * (2 * n) *
          (C_L * n ^ (2 - jmDelta eta0)) *
          (C_L * n ^ (2 - jmDelta eta0)) := by gcongr
    _ = (6 * 512 * 512 * C_L ^ 2) *
          (n : ℝ) ^ (5 - 2 * jmDelta eta0) := by
      rw [← hpower]
      ring
    _ ≤ (jmAuxDegreeReal (jmDelta eta0) n) ^ (2 - jmEta eta0) := hgrowth

/-- Triple-codegree comparison required by the concrete conflict-count
adapter. -/
theorem eventually_jmConflict_triple_comparison
    (L : ℕ → ℕ) {eta0 C_L : ℝ} (heta0 : 0 < eta0) (hCL : 0 ≤ C_L)
    (hL : ∀ᶠ n : ℕ in atTop,
      (L n : ℝ) ≤ C_L * (n : ℝ) ^ (2 - jmDelta eta0)) :
    ∀ᶠ n : ℕ in atTop,
      ((6 * 512 ^ 3 * L n : ℕ) : ℝ) ≤
        (jmAuxDegreeReal (jmDelta eta0) n) ^ (1 - jmEta eta0) := by
  have hgap := (jm_conflict_codegree_exponent_gaps heta0).2
  have hb : 0 < 1 - jmEta eta0 := sub_pos.mpr (jmEta_lt_one heta0)
  have hgrowth := eventually_const_mul_rpow_le_auxDegree_rpow heta0
    (C := 6 * 512 ^ 3 * C_L) (a := 2 - jmDelta eta0)
    (b := 1 - jmEta eta0) (by positivity) hb hgap
  filter_upwards [hL, hgrowth] with n hL hgrowth
  push_cast
  change (805306368 : ℝ) * (L n : ℝ) ≤
    (jmAuxDegreeReal (jmDelta eta0) n) ^ (1 - jmEta eta0)
  calc
    (805306368 : ℝ) * (L n : ℝ) ≤
        805306368 * (C_L * (n : ℝ) ^ (2 - jmDelta eta0)) := by
      gcongr
    _ = (6 * 512 ^ 3 * C_L) * (n : ℝ) ^ (2 - jmDelta eta0) := by ring
    _ ≤ (jmAuxDegreeReal (jmDelta eta0) n) ^ (1 - jmEta eta0) := hgrowth

/-- The three literal numerical hypotheses of
`alternatingCycleConflicts_isBounded_of_maxCodegree`, bundled for direct
construction use. -/
theorem eventually_jmConflictCount_comparisons
    (L : ℕ → ℕ) {eta0 C_L : ℝ} (ell : ℕ)
    (heta0 : 0 < eta0) (hCL : 0 ≤ C_L)
    (hconstant : 512 * C_L ^ 3 ≤ (ell : ℝ))
    (hL : ∀ᶠ n : ℕ in atTop,
      (L n : ℝ) ≤ C_L * (n : ℝ) ^ (2 - jmDelta eta0)) :
    ∀ᶠ n : ℕ in atTop,
      ((512 * n * n * jmOldColors (jmDelta eta0) n *
        L n * L n * L n : ℕ) : ℝ) ≤
          (ell : ℝ) * Real.rpow (jmAuxDegreeReal (jmDelta eta0) n) 3 ∧
      ((3 * 512 * 512 * (n + jmOldColors (jmDelta eta0) n) *
        L n * L n : ℕ) : ℝ) ≤
          (jmAuxDegreeReal (jmDelta eta0) n) ^ (2 - jmEta eta0) ∧
      ((6 * 512 ^ 3 * L n : ℕ) : ℝ) ≤
          (jmAuxDegreeReal (jmDelta eta0) n) ^ (1 - jmEta eta0) := by
  filter_upwards [eventually_jmConflict_degree_comparison L ell heta0 hCL
      hconstant hL,
    eventually_jmConflict_pair_comparison L heta0 hCL hL,
    eventually_jmConflict_triple_comparison L heta0 hCL hL]
      with n hdegree hpair htriple
  exact ⟨hdegree, hpair, htriple⟩

/-- Ceiling-specialized version of the three conflict comparisons.  This is
the direct bridge for a natural pair-codegree bound produced by concentration. -/
theorem eventually_jmCeilConflictCount_comparisons
    {eta0 C C0 : ℝ} (ell : ℕ) (heta0 : 0 < eta0)
    (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hconstant : 512 * (C + C0 + 1) ^ 3 ≤ (ell : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      ((512 * n * n * jmOldColors (jmDelta eta0) n *
        jmPairCodegreeCeil C C0 (jmDelta eta0) n *
        jmPairCodegreeCeil C C0 (jmDelta eta0) n *
        jmPairCodegreeCeil C C0 (jmDelta eta0) n : ℕ) : ℝ) ≤
          (ell : ℝ) * Real.rpow (jmAuxDegreeReal (jmDelta eta0) n) 3 ∧
      ((3 * 512 * 512 * (n + jmOldColors (jmDelta eta0) n) *
        jmPairCodegreeCeil C C0 (jmDelta eta0) n *
        jmPairCodegreeCeil C C0 (jmDelta eta0) n : ℕ) : ℝ) ≤
          (jmAuxDegreeReal (jmDelta eta0) n) ^ (2 - jmEta eta0) ∧
      ((6 * 512 ^ 3 * jmPairCodegreeCeil C C0 (jmDelta eta0) n : ℕ) : ℝ) ≤
          (jmAuxDegreeReal (jmDelta eta0) n) ^ (1 - jmEta eta0) := by
  have hcoefficient : 0 ≤ C + C0 + 1 := by positivity
  have hL := eventually_jmPairCodegreeCeil_cast_le hC hC0
    ((jmDelta_lt_one heta0).trans (by norm_num : (1 : ℝ) < 2))
  exact eventually_jmConflictCount_comparisons
    (jmPairCodegreeCeil C C0 (jmDelta eta0)) ell heta0 hcoefficient
      hconstant hL

/-- One-filter package of the exact-degree facts repeatedly consumed by the
upper construction.  `P` may be the test-index cardinality or any other
explicitly polynomially bounded natural family. -/
theorem eventually_selected_auxDegree_arithmetic
    {eta0 C a : ℝ} (requestedN : ℕ) (P : ℕ → ℕ)
    (heta0 : 0 < eta0) (hC : 0 ≤ C)
    (hP : ∀ᶠ n : ℕ in atTop, (P n : ℝ) ≤ C * (n : ℝ) ^ a) :
    ∀ᶠ n : ℕ in atTop,
      requestedN ≤ n ∧
      jmOldColors (jmDelta eta0) n ≤ n ∧
      0 ≤ jmAuxDegreeReal (jmDelta eta0) n ∧
      ((566231040 * n ^ 8 : ℕ) : ℝ) ≤
        (jmAuxDegreeReal (jmDelta eta0) n) ^ (3 - jmEta eta0) ∧
      (P n : ℝ) ≤ Real.exp ((jmAuxDegreeReal (jmDelta eta0) n) ^
        ((jmEta eta0) ^ 3)) ∧
      (jmAuxDegreeReal (jmDelta eta0) n) ^ (-(jmEta eta0) ^ 3) ≤
        jmCFMError (jmDelta eta0) (jmEta eta0) n ∧
      (jmAuxDegreeReal (jmDelta eta0) n) ^ (-(jmEta eta0) ^ 3) ≤
        (jmRho (jmDelta eta0) n) ^ 2 := by
  filter_upwards [eventually_ge_atTop requestedN,
    eventually_jmOldColors_le (jmDelta_pos heta0),
    eventually_jm_commonLink_n8_le_auxDegree heta0,
    eventually_natPolynomial_le_auxDegree_exponential P heta0 hC hP,
    eventually_auxDegree_cfmError_le_jmCFMError heta0,
    eventually_auxDegree_cfmError_le_rho_sq heta0]
      with n hn hk hW3 hP herror hrho
  exact ⟨hn, hk, jmAuxDegreeReal_nonneg _ _, hW3, hP, herror, hrho⟩

/-! ## A single finite-threshold package -/

/-- All purely numerical requirements used downstream may be enlarged to
one natural threshold.  This packages the fixed CFM degree cutoff, a desired
relative-error bound, the LLL inequality, and `n ≥ requestedN`. -/
theorem eventually_upper_parameter_requirements
    {delta eta epsilon d0 : ℝ} (requestedN : ℕ)
    (hdelta0 : 0 < delta) (hdelta3 : delta < 3)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      requestedN ≤ n ∧
      d0 ≤ jmDegreeScale delta n ∧
      jmCFMError delta eta n ≤ epsilon ∧
      jmLLLFactor delta n ≤ 1 := by
  filter_upwards [eventually_ge_atTop requestedN,
    eventually_jmDegreeScale_ge hdelta3,
    eventually_jmCFMError_le hdelta3 heta hepsilon,
    eventually_jmLLLFactor_le_one hdelta0] with n hn hd herr hlll
  exact ⟨hn, hd, herr, hlll⟩

/-- Fully instantiated numerical package after choosing `eta` below the CFM
threshold and `delta ≪ eta^3`.  Besides a fixed degree cutoff and error
tolerance, it includes polynomial-vs-exponential capacity, the comparison
`d^(-eta^3) ≤ n^(-2delta)`, and the exact completion-LLL inequality. -/
theorem eventually_selected_upper_parameter_requirements
    {eta0 epsilon d0 : ℝ} (requestedN : ℕ) (polynomialExponent : ℝ)
    (heta0 : 0 < eta0) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      requestedN ≤ n ∧
      d0 ≤ jmDegreeScale (jmDelta eta0) n ∧
      jmCFMError (jmDelta eta0) (jmEta eta0) n ≤ epsilon ∧
      jmCFMError (jmDelta eta0) (jmEta eta0) n ≤
        (jmRho (jmDelta eta0) n) ^ 2 ∧
      (n : ℝ) ^ polynomialExponent ≤
        jmExponentialCapacity (jmDelta eta0) (jmEta eta0) n ∧
      jmExactLLLExpression (jmDelta eta0) n ≤ 1 := by
  have hd0 := jmDelta_pos heta0
  have hd1 := jmDelta_lt_one heta0
  have hd3 : jmDelta eta0 < 3 := hd1.trans (by norm_num)
  have he := jmEta_pos heta0
  filter_upwards [eventually_ge_atTop requestedN,
    eventually_jmDegreeScale_ge (d0 := d0) hd3,
    eventually_jmCFMError_le hd3 he hepsilon,
    eventually_gt_atTop (0 : ℕ),
    eventually_rpow_le_jmExponentialCapacity polynomialExponent hd3 he,
    eventually_jmExactLLLExpression_le_one hd0 hd1]
      with n hn hd herr hnpos hcapacity hlll
  exact ⟨hn, hd, herr, jmCFMError_le_rho_sq heta0 hnpos, hcapacity, hlll⟩

end


end Erdos136
