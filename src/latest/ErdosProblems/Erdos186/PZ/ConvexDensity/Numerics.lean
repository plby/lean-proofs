/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Numerical lemmas for the Pham--Zakharov convex-density argument

This file isolates the elementary numerical choices in the proof of the
convex-density lemma.  There are two independent pieces of bookkeeping.

* The fixed choices
  `tau epsilon = epsilon / 10` and
  `alpha d = (d - 1) / (d + 1)` have the required signs and exponent bounds.
* Every positive power of a variable tending to zero absorbs any fixed power
  of `log (1 / delta)`, as well as any fixed multiplicative constant.  The
  final lemmas choose one cutoff which works for a finite family of such
  inequalities.

All limits are taken through positive real numbers.  This matches the role of
`delta` in the paper and avoids assigning analytic meaning to the displayed
expressions at nonpositive inputs.
-/

open Filter Set
open scoped Topology

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-! ## The fixed exponents -/

/-- The exponent denoted by `alpha` in the convex-density argument. -/
def alpha (d : ℕ) : ℝ :=
  ((d : ℝ) - 1) / ((d : ℝ) + 1)

/-- The scale-separation exponent used in the proof of PZ Lemma 1. -/
def tau (epsilon : ℝ) : ℝ :=
  epsilon / 10

@[simp]
theorem alpha_one : alpha 1 = 0 := by
  norm_num [alpha]

theorem alpha_nonneg {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ alpha d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_nonneg (sub_nonneg.mpr hdR) (by positivity)

theorem alpha_lt_one {d : ℕ} (_hd : 1 ≤ d) :
    alpha d < 1 := by
  have hden : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [alpha, div_lt_iff₀ hden]
  linarith

theorem tau_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < tau epsilon := by
  simp only [tau]
  positivity

theorem tau_le_epsilon {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    tau epsilon ≤ epsilon := by
  simp only [tau]
  linarith

theorem tau_lt_one_of_epsilon_le_one {epsilon : ℝ}
    (hepsilon : epsilon ≤ 1) :
    tau epsilon < 1 := by
  simp only [tau]
  linarith

/-- The paper's dimension-dependent smallness condition on `epsilon` implies
the advertised choice `0 < tau < 1`. -/
theorem tau_mem_Ioo_of_epsilon_le_inv_dimension {d : ℕ} {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / ((d : ℝ) + 1)) :
    tau epsilon ∈ Ioo (0 : ℝ) 1 := by
  have hden : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hinv : 1 / ((d : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hden]
    have hd0 : (0 : ℝ) ≤ d := by positivity
    linarith
  exact ⟨tau_pos hepsilon,
    tau_lt_one_of_epsilon_le_one (hepsilon_le.trans hinv)⟩

/-- Under the same smallness condition, the density exponent remains below
one.  This is the numerical margin used when powers of a volume ratio are
compared. -/
theorem alpha_add_epsilon_lt_one {d : ℕ} {epsilon : ℝ}
    (hd : 1 ≤ d)
    (hepsilon_le : epsilon ≤ 1 / ((d : ℝ) + 1)) :
    alpha d + epsilon < 1 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  calc
    alpha d + epsilon
        ≤ alpha d + 1 / ((d : ℝ) + 1) :=
      by linarith
    _ = (d : ℝ) / ((d : ℝ) + 1) := by
      rw [alpha]
      field_simp
      ring
    _ < 1 := by
      rw [div_lt_one hden]
      linarith

/-! ## Powers on the unit interval -/

/-- On `(0,1]`, decreasing a positive real exponent increases the power. -/
theorem le_rpow_of_exponent_le_one {delta exponent : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hexponent : exponent ≤ 1) :
    delta ≤ delta ^ exponent := by
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one hexponent

/-- The interval form used at call sites where the positivity of the exponent
is part of the surrounding parameter package. -/
theorem delta_le_rpow_of_exponent_mem_Ioc {delta exponent : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hexponent : exponent ∈ Ioc (0 : ℝ) 1) :
    delta ≤ delta ^ exponent :=
  le_rpow_of_exponent_le_one hdelta hdelta_one hexponent.2

/-- In particular `delta ≤ delta ^ tau` for the choice made above. -/
theorem le_rpow_tau {delta epsilon : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (_hepsilon : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1) :
    delta ≤ delta ^ tau epsilon := by
  apply le_rpow_of_exponent_le_one hdelta hdelta_one
  exact (tau_lt_one_of_epsilon_le_one hepsilon_le_one).le

/-- Dimension-dependent form of `le_rpow_tau`. -/
theorem le_rpow_tau_of_epsilon_le_inv_dimension {d : ℕ}
    {delta epsilon : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / ((d : ℝ) + 1)) :
    delta ≤ delta ^ tau epsilon := by
  have htau := tau_mem_Ioo_of_epsilon_le_inv_dimension hepsilon hepsilon_le
  exact le_rpow_of_exponent_le_one hdelta hdelta_one htau.2.le

/-! ## Power savings absorb logarithmic losses -/

/-- On the positive unit interval, `log (1 / delta)` is the absolute value of
`log delta`. -/
theorem log_one_div_eq_abs_log {delta : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    Real.log (1 / delta) = |Real.log delta| := by
  rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hdelta.le hdelta_one)]

/-- A positive power of `delta` absorbs a natural power of
`log (1 / delta)` as `delta` tends to zero through positive values. -/
theorem tendsto_rpow_mul_log_one_div_pow_nhdsGT_zero
    {a : ℝ} (b : ℕ) (ha : 0 < a) :
    Tendsto
      (fun delta : ℝ ↦ delta ^ a * (Real.log (1 / delta)) ^ b)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have h :=
    (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (b : ℝ)
      (show -a < 0 by linarith)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
    with delta hdelta
  rw [log_one_div_eq_abs_log hdelta.1 hdelta.2.le]
  rw [Real.rpow_natCast, Real.rpow_neg hdelta.1.le, div_inv_eq_mul]
  ring

/-- Multiplying by a fixed real constant does not affect the preceding
vanishing limit. -/
theorem tendsto_const_mul_log_one_div_pow_mul_rpow_nhdsGT_zero
    (C : ℝ) {a : ℝ} (b : ℕ) (ha : 0 < a) :
    Tendsto
      (fun delta : ℝ ↦ C * (Real.log (1 / delta)) ^ b * delta ^ a)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have h :=
    (tendsto_rpow_mul_log_one_div_pow_nhdsGT_zero b ha).const_mul C
  simpa only [mul_zero] using h.congr' (by
    filter_upwards with delta
    ring)

/-- Eventually a fixed constant and logarithmic power are absorbed by a
positive power of `delta`.  The positive right-hand side is left general so
the result can be used for numerical error budgets other than `1`. -/
theorem eventually_const_mul_log_one_div_pow_mul_rpow_le
    (C : ℝ) {a R : ℝ} (b : ℕ) (ha : 0 < a) (hR : 0 < R) :
    ∀ᶠ delta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      C * (Real.log (1 / delta)) ^ b * delta ^ a ≤ R := by
  have hlt := Filter.Tendsto.eventually_lt_const hR
    (tendsto_const_mul_log_one_div_pow_mul_rpow_nhdsGT_zero C b ha)
  exact hlt.mono fun _ h ↦ h.le

/-- Equivalent eventual formulation with the power saving moved to the
right-hand side. -/
theorem eventually_const_mul_log_one_div_pow_le_rpow_neg
    (C : ℝ) {a : ℝ} (b : ℕ) (ha : 0 < a) :
    ∀ᶠ delta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      C * (Real.log (1 / delta)) ^ b ≤ delta ^ (-a) := by
  filter_upwards
    [eventually_const_mul_log_one_div_pow_mul_rpow_le C b ha zero_lt_one,
      eventually_mem_nhdsWithin]
      with delta hbound hdelta
  change 0 < delta at hdelta
  rw [Real.rpow_neg hdelta.le]
  rw [← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hdelta a)]
  exact hbound

/-! ## Explicit cutoffs, including finite families -/

/-- Choose an explicit positive cutoff below one for one power--log
inequality. -/
theorem exists_deltaZero_const_mul_log_one_div_pow_mul_rpow_le
    (C : ℝ) {a R : ℝ} (b : ℕ) (ha : 0 < a) (hR : 0 < R) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        C * (Real.log (1 / delta)) ^ b * delta ^ a ≤ R := by
  have heventually :=
    eventually_const_mul_log_one_div_pow_mul_rpow_le C b ha hR
  obtain ⟨r, hr, hr_bound⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp heventually
  refine ⟨min r (1 / 2), by positivity, by
    calc
      min r (1 / 2) ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num, ?_⟩
  intro delta hdelta hdelta_cutoff
  apply hr_bound
  exact ⟨hdelta, hdelta_cutoff.trans_le (min_le_left _ _)⟩

/-- A single cutoff works for any finite family of estimates of the form
`C_i * log(1/delta) ^ b_i * delta ^ a_i ≤ R_i`, provided every `a_i` and
`R_i` is positive. -/
theorem exists_deltaZero_forall_const_mul_log_one_div_pow_mul_rpow_le
    {iota : Type*} [Finite iota]
    (C a R : iota → ℝ) (b : iota → ℕ)
    (ha : ∀ i, 0 < a i) (hR : ∀ i, 0 < R i) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        ∀ i, C i * (Real.log (1 / delta)) ^ (b i) * delta ^ (a i) ≤ R i := by
  have heventually :
      ∀ᶠ delta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), ∀ i,
        C i * (Real.log (1 / delta)) ^ (b i) * delta ^ (a i) ≤ R i := by
    apply Filter.eventually_all.mpr
    intro i
    exact eventually_const_mul_log_one_div_pow_mul_rpow_le
      (C i) (b i) (ha i) (hR i)
  obtain ⟨r, hr, hr_bound⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp heventually
  refine ⟨min r (1 / 2), by positivity, by
    calc
      min r (1 / 2) ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num, ?_⟩
  intro delta hdelta hdelta_cutoff i
  exact hr_bound ⟨hdelta, hdelta_cutoff.trans_le (min_le_left _ _)⟩ i

/-- The finite-family cutoff specialized to the normalization used most often
in the proof: every left-hand side is at most `1`. -/
theorem exists_deltaZero_forall_const_mul_log_one_div_pow_mul_rpow_le_one
    {iota : Type*} [Finite iota]
    (C a : iota → ℝ) (b : iota → ℕ)
    (ha : ∀ i, 0 < a i) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        ∀ i, C i * (Real.log (1 / delta)) ^ (b i) * delta ^ (a i) ≤ 1 := by
  simpa using
    (exists_deltaZero_forall_const_mul_log_one_div_pow_mul_rpow_le
      C a (fun _ ↦ (1 : ℝ)) b ha (fun _ ↦ zero_lt_one))

end

end Erdos186.PZ.ConvexDensity
