/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Erdős Problem 186: slowly varying parameters

This file records the elementary analytic estimates used when the parameters in
the Pham--Zakharov argument are chosen as

* `delta κ n = (log log n) ^ (-κ)`,
* `gamma κ K n = delta κ n ^ K`, and
* `mu κ n = delta κ n ^ κ`.

All logarithms and powers here are real.  The definitions are made for every
natural number (so that they are convenient to use in finite statements), while
the hypotheses needed to manipulate negative powers are supplied eventually at
infinity.
-/

namespace Erdos186

open Filter Asymptotics
open scoped Topology

noncomputable section

/-- The iterated real logarithm of a natural number. -/
def logLog (n : ℕ) : ℝ := Real.log (Real.log (n : ℝ))

/-- The principal slowly decaying parameter in the PZ parameter selection. -/
def delta (κ : ℝ) (n : ℕ) : ℝ := logLog n ^ (-κ)

/-- The smaller power of `delta` used for the structural scale. -/
def gamma (κ K : ℝ) (n : ℕ) : ℝ := delta κ n ^ K

/-- The power of `delta` used for the density cutoff. -/
def mu (κ : ℝ) (n : ℕ) : ℝ := delta κ n ^ κ

/-- `log log n` tends to infinity along the natural numbers. -/
theorem tendsto_logLog_atTop : Tendsto logLog atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Eventually the base of all the parameter powers is bigger than one. -/
theorem eventually_one_lt_logLog : ∀ᶠ n : ℕ in atTop, 1 < logLog n :=
  tendsto_logLog_atTop.eventually_gt_atTop 1

/-- The principal parameter is eventually strictly positive. -/
theorem eventually_delta_pos (κ : ℝ) : ∀ᶠ n : ℕ in atTop, 0 < delta κ n := by
  filter_upwards [eventually_one_lt_logLog] with n hn
  exact Real.rpow_pos_of_pos (zero_lt_one.trans hn) _

/-- For positive `κ`, the principal parameter is eventually smaller than one. -/
theorem eventually_delta_lt_one {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, delta κ n < 1 := by
  filter_upwards [eventually_one_lt_logLog] with n hn
  exact Real.rpow_lt_one_of_one_lt_of_neg hn (neg_neg_of_pos hκ)

/-- Eventually `delta` lies in the open unit interval. -/
theorem eventually_delta_mem_Ioo {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, delta κ n ∈ Set.Ioo (0 : ℝ) 1 := by
  filter_upwards [eventually_delta_pos κ, eventually_delta_lt_one hκ] with n hn0 hn1
  exact ⟨hn0, hn1⟩

/-- The parameter `delta` tends to zero for positive `κ`. -/
theorem tendsto_delta_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (delta κ) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ logLog n ^ (-κ)) atTop (𝓝 0)
  simpa only [Function.comp_def] using
    (tendsto_rpow_neg_atTop hκ).comp tendsto_logLog_atTop

/-- Positive powers of `delta` are eventually positive. -/
theorem eventually_gamma_pos (κ : ℝ) {K : ℝ} (_hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, 0 < gamma κ K n := by
  filter_upwards [eventually_delta_pos κ] with n hn
  exact Real.rpow_pos_of_pos hn K

/-- A positive power of a `delta` in `(0,1)` is again in `(0,1)`. -/
theorem eventually_gamma_mem_Ioo {κ K : ℝ} (hκ : 0 < κ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, gamma κ K n ∈ Set.Ioo (0 : ℝ) 1 := by
  filter_upwards [eventually_delta_mem_Ioo hκ] with n hn
  exact ⟨Real.rpow_pos_of_pos hn.1 K, Real.rpow_lt_one hn.1.le hn.2 hK⟩

/-- For positive exponents, `gamma` tends to zero. -/
theorem tendsto_gamma_zero {κ K : ℝ} (hκ : 0 < κ) (hK : 0 < K) :
    Tendsto (gamma κ K) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ delta κ n ^ K) atTop (𝓝 0)
  simpa only [Real.zero_rpow hK.ne'] using
    (tendsto_delta_zero hκ).rpow_const (Or.inr hK.le)

/-- The parameter `mu` is eventually in `(0,1)` when `κ` is positive. -/
theorem eventually_mu_mem_Ioo {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, mu κ n ∈ Set.Ioo (0 : ℝ) 1 := by
  simpa only [mu, gamma] using eventually_gamma_mem_Ioo hκ hκ

/-- The parameter `mu` tends to zero when `κ` is positive. -/
theorem tendsto_mu_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (mu κ) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ delta κ n ^ κ) atTop (𝓝 0)
  simpa only [Real.zero_rpow hκ.ne'] using
    (tendsto_delta_zero hκ).rpow_const (Or.inr hκ.le)

/-- Every fixed real power of `log x` is eventually at most every positive
real power of `x`. -/
theorem eventually_log_rpow_le_rpow (p : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ p ≤ x ^ q := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop p hq).eventuallyLE,
    Real.tendsto_log_atTop.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℝ)]
      with x hx hlog hx0
  simpa [Real.norm_of_nonneg (Real.rpow_nonneg hlog.le p),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le q)] using hx

/-- Natural-number version of power domination over a logarithm. -/
theorem eventually_nat_log_rpow_le_rpow (p : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ p ≤ (n : ℝ) ^ q := by
  exact tendsto_natCast_atTop_atTop.eventually (eventually_log_rpow_le_rpow p hq)

/-- A power of `log log n` is eventually dominated by every positive power of
`log n`. -/
theorem eventually_logLog_rpow_le_log_rpow (p : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, logLog n ^ p ≤ Real.log (n : ℝ) ^ q := by
  have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_log_rpow_le_rpow p hq)
  simpa [logLog] using h

/-- A fixed power of `log n` is little-oh of every positive power of `n`. -/
theorem log_rpow_isLittleO_nat_rpow (p : ℝ) {q : ℝ} (hq : 0 < q) :
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ p) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ q) := by
  simpa [Function.comp_def] using
    (isLittleO_log_rpow_rpow_atTop p hq).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)

/-- A fixed power of `log log n` is little-oh of every positive power of
`log n`. -/
theorem logLog_rpow_isLittleO_log_rpow (p : ℝ) {q : ℝ} (hq : 0 < q) :
    (fun n : ℕ ↦ logLog n ^ p) =o[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ q) := by
  simpa [logLog, Function.comp_def] using
    (isLittleO_log_rpow_rpow_atTop p hq).comp_tendsto
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop))

/-- A fixed power of `log log n` is little-oh of every positive power of `n`. -/
theorem logLog_rpow_isLittleO_nat_rpow (p : ℝ) {q : ℝ} (hq : 0 < q) :
    (fun n : ℕ ↦ logLog n ^ p) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ q) := by
  have h₁ := logLog_rpow_isLittleO_log_rpow p (show (0 : ℝ) < 1 by norm_num)
  have h₂ := log_rpow_isLittleO_nat_rpow 1 hq
  simpa only [Real.rpow_one] using h₁.trans h₂

/-- Inverting the eventual log-versus-power comparison reverses its order. -/
theorem eventually_nat_rpow_neg_le_log_rpow_neg (p : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-q) ≤ Real.log (n : ℝ) ^ (-p) := by
  filter_upwards [eventually_nat_log_rpow_le_rpow p hq,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (0 : ℝ)] with n h hlog hn
  change 0 < Real.log (n : ℝ) at hlog
  rw [Real.rpow_neg hn.le, Real.rpow_neg hlog.le]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hn q) (Real.rpow_pos_of_pos hlog p)).2 h

/-- Negative powers of `log n` are eventually bounded by the PZ `delta`. -/
theorem eventually_log_rpow_neg_le_delta (κ : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ (-q) ≤ delta κ n := by
  filter_upwards [eventually_logLog_rpow_le_log_rpow κ hq,
    eventually_one_lt_logLog,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
      with n h hloglog hlog
  change 0 < Real.log (n : ℝ) at hlog
  rw [delta, Real.rpow_neg hlog.le, Real.rpow_neg (zero_lt_one.trans hloglog).le]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hlog q)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hloglog) κ)).2 h

/-- `delta` decays more slowly than every negative power of `n`. -/
theorem eventually_nat_rpow_neg_le_delta (κ : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-q) ≤ delta κ n := by
  filter_upwards [eventually_nat_rpow_neg_le_log_rpow_neg 1 hq,
    eventually_log_rpow_neg_le_delta κ (show (0 : ℝ) < 1 by norm_num)] with n h₁ h₂
  exact h₁.trans h₂

/-- The concrete `n^(-1/3)` comparison used in the parameter hierarchy. -/
theorem eventually_cubeRoot_inv_le_delta (κ : ℝ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ delta κ n := by
  exact eventually_nat_rpow_neg_le_delta κ (by norm_num)

/-- Negative powers of `log n` are eventually bounded by `gamma` as well.
This is the form used to verify the logarithmic lower bound in the
irreducibility lemma. -/
theorem eventually_log_rpow_neg_le_gamma (κ K : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ (-q) ≤ gamma κ K n := by
  filter_upwards [eventually_logLog_rpow_le_log_rpow (κ * K) hq,
    eventually_one_lt_logLog,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
      with n h hloglog hlog
  change 0 < Real.log (n : ℝ) at hlog
  rw [gamma, delta, ← Real.rpow_mul (zero_lt_one.trans hloglog).le]
  have hexponent : (-κ) * K = -(κ * K) := by ring
  rw [hexponent, Real.rpow_neg hlog.le,
    Real.rpow_neg (zero_lt_one.trans hloglog).le]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hlog q)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hloglog) (κ * K))).2 h

/-- `gamma` decays more slowly than every negative power of `n`. -/
theorem eventually_nat_rpow_neg_le_gamma (κ K : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-q) ≤ gamma κ K n := by
  filter_upwards [eventually_nat_rpow_neg_le_log_rpow_neg 1 hq,
    eventually_log_rpow_neg_le_gamma κ K (show (0 : ℝ) < 1 by norm_num)]
      with n h₁ h₂
  exact h₁.trans h₂

/-- The concrete lower bound on `gamma` required in the dimension-reduction
step of the PZ argument. -/
theorem eventually_cubeRoot_inv_le_gamma (κ K : ℝ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ gamma κ K n := by
  exact eventually_nat_rpow_neg_le_gamma κ K (by norm_num)

/-- If `K ≥ C`, then the choice `gamma = delta^K` satisfies
`gamma ≤ delta^C` on the eventual unit interval. -/
theorem eventually_gamma_le_delta_rpow {κ K C : ℝ} (hκ : 0 < κ) (hCK : C ≤ K) :
    ∀ᶠ n : ℕ in atTop, gamma κ K n ≤ delta κ n ^ C := by
  filter_upwards [eventually_delta_mem_Ioo hκ] with n hn
  exact Real.rpow_le_rpow_of_exponent_ge hn.1 hn.2.le hCK

/-- In particular, a power with exponent at least one is no larger than
`delta` itself. -/
theorem eventually_gamma_le_delta {κ K : ℝ} (hκ : 0 < κ) (hK : 1 ≤ K) :
    ∀ᶠ n : ℕ in atTop, gamma κ K n ≤ delta κ n := by
  simpa only [Real.rpow_one] using
    (eventually_gamma_le_delta_rpow (κ := κ) hκ hK)

/-- If `κ * C ≤ 1`, then `delta ≤ mu^C`; this is the reason `κ` is chosen
after the fixed structural exponent `C`. -/
theorem eventually_delta_le_mu_rpow {κ C : ℝ} (hκ : 0 < κ) (hκC : κ * C ≤ 1) :
    ∀ᶠ n : ℕ in atTop, delta κ n ≤ mu κ n ^ C := by
  filter_upwards [eventually_delta_mem_Ioo hκ] with n hn
  calc
    delta κ n = delta κ n ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ delta κ n ^ (κ * C) :=
      Real.rpow_le_rpow_of_exponent_ge hn.1 hn.2.le hκC
    _ = mu κ n ^ C := by
      rw [Real.rpow_mul hn.1.le]
      rfl

/-- If `κ ≤ K`, the scale `gamma = delta^K` is no larger than
`mu = delta^κ`. -/
theorem eventually_gamma_le_mu {κ K : ℝ} (hκ : 0 < κ) (hκK : κ ≤ K) :
    ∀ᶠ n : ℕ in atTop, gamma κ K n ≤ mu κ n := by
  filter_upwards [eventually_delta_mem_Ioo hκ] with n hn
  exact Real.rpow_le_rpow_of_exponent_ge hn.1 hn.2.le hκK

/-- On the eventual positive range, taking another power of `delta` simply
multiplies its logarithmic exponent. -/
theorem delta_rpow_eq (κ a : ℝ) {n : ℕ} (hn : 0 ≤ logLog n) :
    delta κ n ^ a = logLog n ^ ((-κ) * a) := by
  exact (Real.rpow_mul hn (-κ) a).symm

/-- Explicit logarithmic-power formula for `gamma`. -/
theorem gamma_eq_logLog_rpow (κ K : ℝ) {n : ℕ} (hn : 0 ≤ logLog n) :
    gamma κ K n = logLog n ^ ((-κ) * K) := by
  exact delta_rpow_eq κ K hn

/-- Explicit logarithmic-power formula for `mu`. -/
theorem mu_eq_logLog_rpow (κ : ℝ) {n : ℕ} (hn : 0 ≤ logLog n) :
    mu κ n = logLog n ^ (-(κ ^ 2)) := by
  rw [mu, delta_rpow_eq κ κ hn]
  congr 1
  ring

end

end Erdos186
