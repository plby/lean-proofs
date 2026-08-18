/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Parameters

/-!
# Asymptotics of the source parameters used in the PZ iteration

The final one-step construction chooses the paper's parameters from the
cardinality of the initial counterexample.  This file records two elementary
consequences which are repeatedly needed by the finite branch assembly:

* `delta` is eventually much smaller than `mu` when `0 < kappa < 1`;
* although `mu` tends to zero, `mu N * N` tends to infinity.

Both statements retain the exact definitions in `Parameters`; no surrogate
power law or additional hypothesis is introduced.
-/

namespace Erdos186.PZ

open Filter Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The ratio `delta / mu` tends to zero in the source range
`0 < kappa < 1`. -/
theorem tendsto_delta_div_mu_zero {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1) :
    Tendsto (fun N : ℕ ↦ delta kappa N / mu kappa N)
      atTop (𝓝 0) := by
  let exponent : ℝ := kappa * (1 - kappa)
  have hexponent : 0 < exponent :=
    mul_pos hkappa (sub_pos.mpr hkappaOne)
  have htendsto :
      Tendsto (fun N : ℕ ↦ logLog N ^ (-exponent)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hexponent).comp tendsto_logLog_atTop
  apply htendsto.congr'
  filter_upwards [eventually_one_lt_logLog] with N hN
  have hlog : 0 < logLog N := zero_lt_one.trans hN
  rw [delta, mu_eq_logLog_rpow kappa hlog.le]
  rw [← Real.rpow_sub hlog]
  congr 1
  dsimp only [exponent]
  ring

/-- In particular the source separation `delta < mu / c` holds eventually
for every fixed positive divisor `c`. -/
theorem eventually_delta_lt_mu_div {kappa c : ℝ}
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, delta kappa N < mu kappa N / c := by
  have hratio :=
    (tendsto_delta_div_mu_zero hkappa hkappaOne).eventually_lt_const
      (inv_pos.mpr hc)
  filter_upwards [hratio, eventually_mu_mem_Ioo hkappa] with N hratioN hmuN
  calc
    delta kappa N =
        (delta kappa N / mu kappa N) * mu kappa N :=
      (div_mul_cancel₀ _ hmuN.1.ne').symm
    _ < c⁻¹ * mu kappa N :=
      mul_lt_mul_of_pos_right hratioN hmuN.1
    _ = mu kappa N / c := by
      rw [div_eq_mul_inv]
      ring

/-- The exact separation used by the half-core intersection constructor. -/
theorem eventually_delta_lt_mu_div_eight {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1) :
    ∀ᶠ N : ℕ in atTop, delta kappa N < mu kappa N / 8 := by
  exact eventually_delta_lt_mu_div hkappa hkappaOne (by norm_num)

/-- The slowly decaying density cutoff still leaves an unbounded number of
points: `mu kappa N * N` tends to infinity. -/
theorem tendsto_mu_mul_natCast_atTop (kappa : ℝ) :
    Tendsto (fun N : ℕ ↦ mu kappa N * (N : ℝ)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      C ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  have hlower : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ mu kappa N := by
    simpa only [mu, gamma] using
      eventually_nat_rpow_neg_le_gamma kappa kappa
        (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hgrowth, hlower, eventually_gt_atTop (0 : ℕ)]
    with N hgrowthN hlowerN hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    C ≤ (N : ℝ) ^ (1 / 2 : ℝ) := hgrowthN
    _ = (N : ℝ) ^ (-(1 / 2 : ℝ) + 1) := by
      congr 1
      ring
    _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ 1 :=
      Real.rpow_add hNreal _ _
    _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) := by
      rw [Real.rpow_one]
    _ ≤ mu kappa N * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hlowerN hNreal.le

/-- Threshold form of `tendsto_mu_mul_natCast_atTop`, convenient for finite
parameter selection. -/
theorem eventually_const_le_mu_mul_natCast (kappa C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C ≤ mu kappa N * (N : ℝ) :=
  (tendsto_mu_mul_natCast_atTop kappa).eventually_ge_atTop C

/-- The power available in a dense selected CFP dilation dominates every
fixed constant even when both `gamma` and `delta` use the slowly varying
source choice.  This is the asymptotic input in the functional-slab
low-rank inequality. -/
theorem tendsto_gamma_mul_delta_rpow_mul_nat_rpow_atTop
    (kappa K : ℝ) {eta : ℝ} (heta : 0 < eta) :
    Tendsto
      (fun N : ℕ ↦ gamma kappa K N * delta kappa N ^ eta *
        (N : ℝ) ^ eta)
      atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      C ≤ (N : ℝ) ^ (eta / 2) :=
    ((tendsto_rpow_atTop (half_pos heta)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  have hgamma : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(eta / 4)) ≤ gamma kappa K N :=
    eventually_nat_rpow_neg_le_gamma kappa K (div_pos heta (by norm_num))
  have hdelta : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(1 / 4 : ℝ)) ≤ delta kappa N :=
    eventually_nat_rpow_neg_le_delta kappa (by norm_num)
  filter_upwards [hgrowth, hgamma, hdelta, eventually_delta_pos kappa,
      eventually_gt_atTop (0 : ℕ)]
    with N hgrowthN hgammaN hdeltaN hdeltaPos hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdeltaPower :
      (N : ℝ) ^ (-(eta / 4)) ≤ delta kappa N ^ eta := by
    calc
      (N : ℝ) ^ (-(eta / 4)) =
          ((N : ℝ) ^ (-(1 / 4 : ℝ))) ^ eta := by
        rw [← Real.rpow_mul hNreal.le]
        congr 1
        ring
      _ ≤ delta kappa N ^ eta :=
        Real.rpow_le_rpow (Real.rpow_nonneg hNreal.le _)
          hdeltaN heta.le
  have hgammaNonneg : 0 ≤ gamma kappa K N := by
    exact Real.rpow_nonneg hdeltaPos.le K
  calc
    C ≤ (N : ℝ) ^ (eta / 2) := hgrowthN
    _ = (N : ℝ) ^ (-(eta / 4)) *
          (N : ℝ) ^ (-(eta / 4)) * (N : ℝ) ^ eta := by
      rw [← Real.rpow_add hNreal, ← Real.rpow_add hNreal]
      congr 1
      ring
    _ ≤ gamma kappa K N * delta kappa N ^ eta * (N : ℝ) ^ eta := by
      gcongr

/-- Eventual fixed-bound form of the preceding growth theorem. -/
theorem eventually_const_le_gamma_mul_delta_rpow_mul_nat_rpow
    (kappa K : ℝ) {eta : ℝ} (heta : 0 < eta) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C ≤ gamma kappa K N * delta kappa N ^ eta * (N : ℝ) ^ eta :=
  (tendsto_gamma_mul_delta_rpow_mul_nat_rpow_atTop kappa K heta).eventually_ge_atTop C

/-- The logarithmic cost of the slowly varying parameter is negligible
compared with `log N`.  This is the source of the positive, but
counterexample-dependent, same-dimension excess gain. -/
theorem tendsto_neg_log_delta_div_log_zero (kappa : ℝ) :
    Tendsto
      (fun N : ℕ ↦ -Real.log (delta kappa N) /
        Real.log (N : ℝ))
      atTop (𝓝 0) := by
  have hlogLogLog :
      (fun N : ℕ ↦ Real.log (logLog N)) =o[atTop]
        (fun N : ℕ ↦ logLog N) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
        (by norm_num : (0 : ℝ) < 1)).comp_tendsto tendsto_logLog_atTop
  have hlogLog :
      (fun N : ℕ ↦ logLog N) =o[atTop]
        (fun N : ℕ ↦ Real.log (N : ℝ)) := by
    simpa only [Real.rpow_one] using
      logLog_rpow_isLittleO_log_rpow (1 : ℝ)
        (by norm_num : (0 : ℝ) < 1)
  have hideal :
      (fun N : ℕ ↦ kappa * Real.log (logLog N)) =o[atTop]
        (fun N : ℕ ↦ Real.log (N : ℝ)) :=
    (hlogLogLog.trans hlogLog).const_mul_left kappa
  have htendsto := hideal.tendsto_div_nhds_zero
  apply htendsto.congr'
  filter_upwards [eventually_one_lt_logLog] with N hN
  have hlog : 0 < logLog N := zero_lt_one.trans hN
  congr 1
  rw [delta, Real.log_rpow hlog]
  ring

/-- The corresponding logarithmic cost for `mu = delta^kappa` is also
negligible compared with `log N`. -/
theorem tendsto_neg_log_mu_div_log_zero (kappa : ℝ) :
    Tendsto
      (fun N : ℕ ↦ -Real.log (mu kappa N) /
        Real.log (N : ℝ))
      atTop (𝓝 0) := by
  have htendsto :=
    (tendsto_neg_log_delta_div_log_zero kappa).const_mul kappa
  have htendsto' :
      Tendsto
        (fun N : ℕ ↦ kappa *
          (-Real.log (delta kappa N) / Real.log (N : ℝ)))
        atTop (𝓝 0) := by
    simpa using htendsto
  apply htendsto'.congr'
  filter_upwards [eventually_delta_pos kappa] with N hdelta
  rw [mu, Real.log_rpow hdelta]
  ring

/-- A fixed positive rank gap absorbs the frozen convex-scale and box
constant costs uniformly for every later population above the square root
of the initial one. -/
theorem eventually_frozen_rankDrop_logBudget
    {kappa saving densityCeiling : ℝ}
    (hkappa : 0 < kappa) (hsaving : 0 < saving)
    (hdensityCeiling : 0 ≤ densityCeiling) (boxConstant : ℝ) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ currentCard : ℕ,
        Real.sqrt (initialCard : ℝ) ≤ (currentCard : ℝ) →
        Real.log boxConstant +
            densityCeiling * (-Real.log (mu kappa initialCard)) -
              Real.log (1 / 2) ≤
          saving * Real.log (currentCard : ℝ) := by
  let fixedCost : ℝ := Real.log boxConstant - Real.log (1 / 2)
  let ratioCap : ℝ := saving / (4 * (densityCeiling + 1))
  have hdenom : 0 < 4 * (densityCeiling + 1) := by positivity
  have hratioCap : 0 < ratioCap := div_pos hsaving hdenom
  have hfixed : ∀ᶠ N : ℕ in atTop,
      fixedCost ≤ saving / 4 * Real.log (N : ℝ) :=
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by positivity : 0 < saving / 4)).eventually_ge_atTop fixedCost
  have hratio : ∀ᶠ N : ℕ in atTop,
      -Real.log (mu kappa N) / Real.log (N : ℝ) < ratioCap :=
    (tendsto_neg_log_mu_div_log_zero kappa).eventually_lt_const hratioCap
  filter_upwards [hfixed, hratio, eventually_mu_mem_Ioo hkappa,
      eventually_gt_atTop (1 : ℕ)]
    with initialCard hfixedN hratioN hmuN hinitial
  intro currentCard hsqrt
  have hinitialPos : (0 : ℝ) < (initialCard : ℝ) := by
    exact_mod_cast (show 0 < initialCard by omega)
  have hlogInitialPos : 0 < Real.log (initialCard : ℝ) :=
    Real.log_pos (by exact_mod_cast hinitial)
  have hnegLogMu : 0 ≤ -Real.log (mu kappa initialCard) := by
    have := Real.log_nonpos hmuN.1.le hmuN.2.le
    linarith
  have hratioNonneg :
      0 ≤ -Real.log (mu kappa initialCard) /
        Real.log (initialCard : ℝ) :=
    div_nonneg hnegLogMu hlogInitialPos.le
  have hdensityRatio :
      densityCeiling *
          (-Real.log (mu kappa initialCard) /
            Real.log (initialCard : ℝ)) ≤ saving / 4 := by
    calc
      densityCeiling *
          (-Real.log (mu kappa initialCard) /
            Real.log (initialCard : ℝ)) ≤
          (densityCeiling + 1) *
            (-Real.log (mu kappa initialCard) /
              Real.log (initialCard : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hratioNonneg
      _ ≤ (densityCeiling + 1) * ratioCap :=
        mul_le_mul_of_nonneg_left hratioN.le (by linarith)
      _ = saving / 4 := by
        dsimp only [ratioCap]
        field_simp
  have hslow :
      densityCeiling * (-Real.log (mu kappa initialCard)) ≤
        saving / 4 * Real.log (initialCard : ℝ) := by
    calc
      densityCeiling * (-Real.log (mu kappa initialCard)) =
          (densityCeiling *
            (-Real.log (mu kappa initialCard) /
              Real.log (initialCard : ℝ))) *
                Real.log (initialCard : ℝ) := by
        field_simp
      _ ≤ saving / 4 * Real.log (initialCard : ℝ) :=
        mul_le_mul_of_nonneg_right hdensityRatio hlogInitialPos.le
  have hsqrtPos : 0 < Real.sqrt (initialCard : ℝ) :=
    Real.sqrt_pos.2 hinitialPos
  have hlogSqrt :
      Real.log (initialCard : ℝ) / 2 ≤
        Real.log (currentCard : ℝ) := by
    rw [← Real.log_sqrt hinitialPos.le]
    exact Real.log_le_log hsqrtPos hsqrt
  dsimp only [fixedCost] at hfixedN
  nlinarith

/-- Cardinal-threshold form of `eventually_frozen_rankDrop_logBudget`. -/
theorem exists_frozen_rankDrop_logBudget_threshold
    {kappa saving densityCeiling : ℝ}
    (hkappa : 0 < kappa) (hsaving : 0 < saving)
    (hdensityCeiling : 0 ≤ densityCeiling) (boxConstant : ℝ) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {initialCard currentCard : ℕ}, threshold ≤ initialCard →
        Real.sqrt (initialCard : ℝ) ≤ (currentCard : ℝ) →
        Real.log boxConstant +
            densityCeiling * (-Real.log (mu kappa initialCard)) -
              Real.log (1 / 2) ≤
          saving * Real.log (currentCard : ℝ) := by
  obtain ⟨growthThreshold, hgrowth⟩ := eventually_atTop.1
    (eventually_frozen_rankDrop_logBudget hkappa hsaving hdensityCeiling
      boxConstant)
  let threshold := max 2 growthThreshold
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro initialCard currentCard hinitial hsqrt
  exact hgrowth initialCard
    ((le_max_right 2 growthThreshold).trans hinitial) currentCard hsqrt

/-- A polynomial CFP loss with exponent strictly below one is negligible
against the source mass `mu N * N`, even after the logarithmic loss factor.
This is the quantitative comparison used to retain almost all of the
canonical core in the intersection step. -/
theorem eventually_const_mul_nat_rpow_mul_log_le_mu_mul_natCast
    (kappa : ℝ) {eta C : ℝ} (heta : eta < 1) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ eta * Real.log (N : ℝ) ≤
        mu kappa N * (N : ℝ) := by
  let q : ℝ := (1 - eta) / 4
  have hq : 0 < q := div_pos (sub_pos.mpr heta) (by norm_num)
  have hconstant : ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ q :=
    ((tendsto_rpow_atTop hq).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  have hlog : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ≤ (N : ℝ) ^ q := by
    simpa only [Real.rpow_one] using
      eventually_nat_log_rpow_le_rpow (1 : ℝ) hq
  have hmu : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-q) ≤ mu kappa N := by
    simpa only [mu, gamma] using
      eventually_nat_rpow_neg_le_gamma kappa kappa hq
  filter_upwards [hconstant, hlog, hmu, eventually_gt_atTop (1 : ℕ)]
    with N hconstantN hlogN hmuN hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN.le
  have hlogNonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNone
  have hpowEtaNonneg : 0 ≤ (N : ℝ) ^ eta :=
    Real.rpow_nonneg hNreal.le _
  have hpowQNonneg : 0 ≤ (N : ℝ) ^ q :=
    Real.rpow_nonneg hNreal.le _
  have hexponents : q + eta + q ≤ 1 - q := by
    dsimp only [q]
    linarith
  calc
    C * (N : ℝ) ^ eta * Real.log (N : ℝ) ≤
        (N : ℝ) ^ q * (N : ℝ) ^ eta * (N : ℝ) ^ q := by
      gcongr
    _ = (N : ℝ) ^ (q + eta + q) := by
      rw [Real.rpow_add hNreal, Real.rpow_add hNreal]
    _ ≤ (N : ℝ) ^ (1 - q) :=
      Real.rpow_le_rpow_of_exponent_le hNone hexponents
    _ = (N : ℝ) ^ (-q + 1) := by
      congr 1
      ring
    _ = (N : ℝ) ^ (-q) * (N : ℝ) ^ 1 :=
      Real.rpow_add hNreal _ _
    _ = (N : ℝ) ^ (-q) * (N : ℝ) := by
      rw [Real.rpow_one]
    _ ≤ mu kappa N * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hmuN hNreal.le

/-- The product `gamma * mu * N` also tends to infinity.  Choosing the slab
thickness proportional to `gamma` leaves precisely this scale in the
weighted-radius inequality. -/
theorem tendsto_gamma_mul_mu_mul_natCast_atTop (kappa K : ℝ) :
    Tendsto
      (fun N : ℕ ↦ gamma kappa K N * mu kappa N * (N : ℝ))
      atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      C ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  have hgamma : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ gamma kappa K N :=
    eventually_nat_rpow_neg_le_gamma kappa K (by norm_num)
  have hmu : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ mu kappa N := by
    simpa only [mu, gamma] using
      eventually_nat_rpow_neg_le_gamma kappa kappa
        (by norm_num : (0 : ℝ) < 1 / 3)
  filter_upwards [hgrowth, hgamma, hmu, eventually_delta_pos kappa,
      eventually_gt_atTop (0 : ℕ)]
    with N hgrowthN hgammaN hmuN hdeltaPos hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hgammaNonneg : 0 ≤ gamma kappa K N :=
    Real.rpow_nonneg hdeltaPos.le K
  calc
    C ≤ (N : ℝ) ^ (1 / 3 : ℝ) := hgrowthN
    _ = (N : ℝ) ^
          (-(1 / 3 : ℝ) + -(1 / 3 : ℝ) + 1) := by
      congr 1
      ring
    _ = (N : ℝ) ^ (-(1 / 3 : ℝ) + -(1 / 3 : ℝ)) *
          (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_add hNreal _ _
    _ = (N : ℝ) ^ (-(1 / 3 : ℝ)) *
          (N : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_add hNreal]
    _ = (N : ℝ) ^ (-(1 / 3 : ℝ)) *
          (N : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) := by
      rw [Real.rpow_one]
    _ ≤ gamma kappa K N * mu kappa N * (N : ℝ) := by
      gcongr

/-- Eventual fixed-bound form of `gamma * mu * N → ∞`. -/
theorem eventually_const_le_gamma_mul_mu_mul_natCast
    (kappa K C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C ≤ gamma kappa K N * mu kappa N * (N : ℝ) :=
  (tendsto_gamma_mul_mu_mul_natCast_atTop kappa K).eventually_ge_atTop C

/-! ## Slow variation across the retained square-root range -/

/-- For positive `kappa`, the logarithmic cost `-log (mu kappa N)` tends to
infinity.  This absorbs every fixed John/replacement box constant in the
same-rank branch. -/
theorem tendsto_neg_log_mu_atTop {kappa : ℝ} (hkappa : 0 < kappa) :
    Tendsto (fun N : ℕ ↦ -Real.log (mu kappa N)) atTop atTop := by
  have htripleLog :
      Tendsto (fun N : ℕ ↦ Real.log (logLog N)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_logLog_atTop
  have hscaled := htripleLog.const_mul_atTop
    (show 0 < kappa ^ 2 by positivity)
  apply hscaled.congr'
  filter_upwards [eventually_one_lt_logLog] with N hlogLog
  rw [mu_eq_logLog_rpow kappa (by linarith),
    Real.log_rpow (by linarith : 0 < logLog N)]
  ring

/-- Uniform threshold absorbing a fixed constant into `-log mu`. -/
theorem exists_neg_log_mu_absorption_threshold
    {kappa : ℝ} (hkappa : 0 < kappa) (C : ℝ) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {N : ℕ}, threshold ≤ N → C ≤ -Real.log (mu kappa N) := by
  obtain ⟨growthThreshold, hgrowth⟩ := eventually_atTop.1
    ((tendsto_neg_log_mu_atTop hkappa).eventually_ge_atTop C)
  let threshold := max 2 growthThreshold
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro N hN
  exact hgrowth N ((le_max_right 2 growthThreshold).trans hN)

/-- Exact fixed-constant budget used by the source same-rank constructor. -/
theorem exists_sameRank_fixedConstantBudget_threshold
    {zeta tau kappa : ℝ} (hzeta : 0 < zeta) (htau : 0 < tau)
    (hkappa : 0 < kappa) (C : ℝ) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {currentCard : ℕ}, threshold ≤ currentCard →
        16 * Real.log C ≤
          zeta * tau * (-Real.log (mu kappa currentCard)) := by
  have hcoefficient : 0 < zeta * tau := mul_pos hzeta htau
  obtain ⟨threshold, hthresholdTwo, habsorb⟩ :=
    exists_neg_log_mu_absorption_threshold hkappa
      (16 * Real.log C / (zeta * tau))
  refine ⟨threshold, hthresholdTwo, ?_⟩
  intro currentCard hlarge
  simpa [mul_comm] using
    ((div_le_iff₀ hcoefficient).mp (habsorb hlarge))

/-- Once the initial population is large, `-log mu` changes by at most a
factor two on every population above its square root.  This is the uniform
slow-variation comparison needed when a same-rank gain is frozen from the
initial counterexample but later applied to every state in the finite trace. -/
theorem eventually_neg_log_mu_le_two_mul_of_sqrt_le (kappa : ℝ) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ currentCard : ℕ, 2 ≤ currentCard →
        Real.sqrt (initialCard : ℝ) ≤ (currentCard : ℝ) →
        -Real.log (mu kappa initialCard) ≤
          2 * (-Real.log (mu kappa currentCard)) := by
  have hlarge : ∀ᶠ initialCard : ℕ in atTop,
      (4 : ℝ) ≤ logLog initialCard :=
    tendsto_logLog_atTop.eventually_ge_atTop 4
  filter_upwards [hlarge] with initialCard hlogLogInitial
  intro currentCard hcurrentTwo hsqrt
  have hcurrentPos : (0 : ℝ) < (currentCard : ℝ) := by
    exact_mod_cast (show 0 < currentCard by omega)
  have hinitialTwo : 2 ≤ initialCard := by
    by_contra hnot
    have hinitialLe : initialCard ≤ 1 := by omega
    interval_cases initialCard <;>
      norm_num [logLog] at hlogLogInitial
  have hinitialPos : (0 : ℝ) < (initialCard : ℝ) := by
    exact_mod_cast (show 0 < initialCard by omega)
  have hlogInitialPos : 0 < Real.log (initialCard : ℝ) :=
    Real.log_pos (by exact_mod_cast hinitialTwo)
  have hsqrtPos : 0 < Real.sqrt (initialCard : ℝ) :=
    Real.sqrt_pos.2 hinitialPos
  have hlogSqrtLe :
      Real.log (initialCard : ℝ) / 2 ≤
        Real.log (currentCard : ℝ) := by
    rw [← Real.log_sqrt hinitialPos.le]
    exact Real.log_le_log hsqrtPos hsqrt
  have hhalfLogPos : 0 < Real.log (initialCard : ℝ) / 2 :=
    half_pos hlogInitialPos
  have hlogLogLower :
      logLog initialCard - Real.log 2 ≤ logLog currentCard := by
    have h := Real.log_le_log hhalfLogPos hlogSqrtLe
    rw [Real.log_div hlogInitialPos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
    simpa only [logLog] using h
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hsqrtLogLog :
      Real.sqrt (logLog initialCard) ≤ logLog initialCard - 1 := by
    have hnonneg : 0 ≤ logLog initialCard := hlogLogInitial.trans' (by norm_num)
    have hsqrtNonneg := Real.sqrt_nonneg (logLog initialCard)
    have hsquare := Real.sq_sqrt hnonneg
    nlinarith
  have hsqrtLogLogLe :
      Real.sqrt (logLog initialCard) ≤ logLog currentCard := by
    calc
      Real.sqrt (logLog initialCard) ≤ logLog initialCard - 1 :=
        hsqrtLogLog
      _ ≤ logLog initialCard - Real.log 2 := by linarith
      _ ≤ logLog currentCard := hlogLogLower
  have hsqrtLogLogPos : 0 < Real.sqrt (logLog initialCard) :=
    Real.sqrt_pos.2 (by linarith)
  have htripleLog :
      Real.log (logLog initialCard) ≤
        2 * Real.log (logLog currentCard) := by
    have h := Real.log_le_log hsqrtLogLogPos hsqrtLogLogLe
    rw [Real.log_sqrt (by linarith : 0 ≤ logLog initialCard)] at h
    linarith
  have hlogLogCurrentPos : 0 < logLog currentCard :=
    hsqrtLogLogPos.trans_le hsqrtLogLogLe
  have hmuInitial :
      -Real.log (mu kappa initialCard) =
        kappa ^ 2 * Real.log (logLog initialCard) := by
    rw [mu_eq_logLog_rpow kappa (by linarith),
      Real.log_rpow (by linarith : 0 < logLog initialCard)]
    ring
  have hmuCurrent :
      -Real.log (mu kappa currentCard) =
        kappa ^ 2 * Real.log (logLog currentCard) := by
    rw [mu_eq_logLog_rpow kappa hlogLogCurrentPos.le,
      Real.log_rpow hlogLogCurrentPos]
    ring
  rw [hmuInitial, hmuCurrent]
  nlinarith [mul_le_mul_of_nonneg_left htripleLog (sq_nonneg kappa)]

/-- Cardinal-threshold form of
`eventually_neg_log_mu_le_two_mul_of_sqrt_le`. -/
theorem exists_neg_log_mu_sqrt_range_threshold (kappa : ℝ) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {initialCard currentCard : ℕ},
        threshold ≤ initialCard → 2 ≤ currentCard →
        Real.sqrt (initialCard : ℝ) ≤ (currentCard : ℝ) →
        -Real.log (mu kappa initialCard) ≤
          2 * (-Real.log (mu kappa currentCard)) := by
  obtain ⟨growthThreshold, hgrowth⟩ := eventually_atTop.1
    (eventually_neg_log_mu_le_two_mul_of_sqrt_le kappa)
  let threshold := max 2 growthThreshold
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro initialCard currentCard hinitial hcurrent hsqrt
  exact hgrowth initialCard (le_max_right _ _ |>.trans hinitial)
    currentCard hcurrent hsqrt

end

end Erdos186.PZ
