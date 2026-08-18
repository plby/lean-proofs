/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.SourceParameterAsymptotics

/-!
# Source growth at a frozen initial population

The terminal replacement state retains at least the square root of the
initial population.  These variants of the source growth estimates therefore
use only half of the available polynomial exponent, while all logarithmic
parameter powers remain frozen at the initial cardinality.
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- A frozen `gamma` times any positive power of the initial population tends
to infinity. -/
theorem tendsto_gamma_mul_nat_rpow_atTop
    (kappa K : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ gamma kappa K N * (N : ℝ) ^ a)
      atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  have hgrowth : ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ (a / 2) :=
    ((tendsto_rpow_atTop (half_pos ha)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  have hgamma : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(a / 2)) ≤ gamma kappa K N :=
    eventually_nat_rpow_neg_le_gamma kappa K (half_pos ha)
  filter_upwards [hgrowth, hgamma, eventually_gt_atTop (0 : ℕ)]
    with N hgrowthN hgammaN hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    C ≤ (N : ℝ) ^ (a / 2) := hgrowthN
    _ = (N : ℝ) ^ (-(a / 2)) * (N : ℝ) ^ a := by
      rw [← Real.rpow_add hNreal]
      congr 1
      ring
    _ ≤ gamma kappa K N * (N : ℝ) ^ a := by
      gcongr

/-- Threshold form of `tendsto_gamma_mul_nat_rpow_atTop`. -/
theorem eventually_const_le_gamma_mul_nat_rpow
    (kappa K : ℝ) {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C ≤ gamma kappa K N * (N : ℝ) ^ a :=
  (tendsto_gamma_mul_nat_rpow_atTop kappa K ha).eventually_ge_atTop C

/-- A fixed natural power of `gamma`, one factor of `mu`, and every positive
population power still tend to infinity. -/
theorem tendsto_gamma_natPow_mul_mu_mul_nat_rpow_atTop
    (kappa K : ℝ) (p : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦
      gamma kappa K N ^ p * mu kappa N * (N : ℝ) ^ a)
      atTop atTop := by
  have hbase := tendsto_gamma_mul_nat_rpow_atTop
    kappa (K * (p : ℝ) + kappa) ha
  apply hbase.congr'
  filter_upwards [eventually_delta_pos kappa] with N hdelta
  have hcombine : gamma kappa K N ^ p * mu kappa N =
      gamma kappa (K * (p : ℝ) + kappa) N := by
    unfold gamma mu
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdelta.le,
      ← Real.rpow_add hdelta]
  rw [hcombine]

/-- Threshold form of the preceding frozen power-product growth. -/
theorem eventually_const_le_gamma_natPow_mul_mu_mul_nat_rpow
    (kappa K : ℝ) (p : ℕ) {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C ≤ gamma kappa K N ^ p * mu kappa N * (N : ℝ) ^ a :=
  (tendsto_gamma_natPow_mul_mu_mul_nat_rpow_atTop
    kappa K p ha).eventually_ge_atTop C

/-- The logarithm also dominates the two frozen slowly varying losses. -/
theorem tendsto_gamma_mul_mu_mul_log_atTop (kappa K : ℝ) :
    Tendsto (fun N : ℕ ↦
      gamma kappa K N * mu kappa N * Real.log (N : ℝ))
      atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      C ≤ Real.log (N : ℝ) ^ (1 / 3 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)).eventually_ge_atTop C
  have hgamma : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ gamma kappa K N :=
    eventually_log_rpow_neg_le_gamma kappa K (by norm_num)
  have hmu : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ mu kappa N := by
    simpa only [mu, gamma] using
      eventually_log_rpow_neg_le_gamma kappa kappa
        (by norm_num : (0 : ℝ) < 1 / 3)
  filter_upwards [hgrowth, hgamma, hmu,
      (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
      eventually_delta_pos kappa]
    with N hgrowthN hgammaN hmuN hlogN hdeltaN
  have hgammaNonneg : 0 ≤ gamma kappa K N :=
    Real.rpow_nonneg hdeltaN.le _
  have hlog : 0 < Real.log (N : ℝ) := hlogN
  calc
    C ≤ Real.log (N : ℝ) ^ (1 / 3 : ℝ) := hgrowthN
    _ = Real.log (N : ℝ) ^
          (-(1 / 3 : ℝ) + -(1 / 3 : ℝ) + 1) := by
      congr 1
      ring
    _ = Real.log (N : ℝ) ^
          (-(1 / 3 : ℝ) + -(1 / 3 : ℝ)) *
            Real.log (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_add hlog _ _
    _ = Real.log (N : ℝ) ^ (-(1 / 3 : ℝ)) *
          Real.log (N : ℝ) ^ (-(1 / 3 : ℝ)) *
            Real.log (N : ℝ) := by
      rw [Real.rpow_add hlog, Real.rpow_one]
    _ ≤ gamma kappa K N * mu kappa N * Real.log (N : ℝ) := by
      gcongr

/-- Fixed-bound form of `gamma * mu * log N → ∞`. -/
theorem eventually_const_le_gamma_mul_mu_mul_log
    (kappa K C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C ≤ gamma kappa K N * mu kappa N * Real.log (N : ℝ) :=
  (tendsto_gamma_mul_mu_mul_log_atTop kappa K).eventually_ge_atTop C

/-- The low-rank slab scale remains unbounded when the candidate population
is only known to be at least the square root of the frozen population. -/
theorem tendsto_gamma_mul_delta_rpow_mul_nat_half_rpow_atTop
    (kappa K : ℝ) {eta : ℝ} (heta : 0 < eta) :
    Tendsto
      (fun N : ℕ ↦ gamma kappa K N * delta kappa N ^ eta *
        (N : ℝ) ^ (eta / 2))
      atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      C ≤ (N : ℝ) ^ (eta / 4) :=
    ((tendsto_rpow_atTop (div_pos heta (by norm_num))).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  have hgamma : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(eta / 8)) ≤ gamma kappa K N :=
    eventually_nat_rpow_neg_le_gamma kappa K
      (div_pos heta (by norm_num))
  have hdelta : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(1 / 8 : ℝ)) ≤ delta kappa N :=
    eventually_nat_rpow_neg_le_delta kappa (by norm_num)
  filter_upwards [hgrowth, hgamma, hdelta, eventually_delta_pos kappa,
      eventually_gt_atTop (0 : ℕ)]
    with N hgrowthN hgammaN hdeltaN hdeltaPos hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdeltaPower :
      (N : ℝ) ^ (-(eta / 8)) ≤ delta kappa N ^ eta := by
    calc
      (N : ℝ) ^ (-(eta / 8)) =
          ((N : ℝ) ^ (-(1 / 8 : ℝ))) ^ eta := by
        rw [← Real.rpow_mul hNreal.le]
        congr 1
        ring
      _ ≤ delta kappa N ^ eta :=
        Real.rpow_le_rpow (Real.rpow_nonneg hNreal.le _)
          hdeltaN heta.le
  have hgammaNonneg : 0 ≤ gamma kappa K N := by
    exact Real.rpow_nonneg hdeltaPos.le K
  calc
    C ≤ (N : ℝ) ^ (eta / 4) := hgrowthN
    _ = (N : ℝ) ^ (-(eta / 8)) *
          (N : ℝ) ^ (-(eta / 8)) *
            (N : ℝ) ^ (eta / 2) := by
      rw [← Real.rpow_add hNreal, ← Real.rpow_add hNreal]
      congr 1
      ring
    _ ≤ gamma kappa K N * delta kappa N ^ eta *
          (N : ℝ) ^ (eta / 2) := by
      gcongr

/-- Fixed-bound form of the frozen square-root low-rank growth theorem. -/
theorem eventually_const_le_gamma_mul_delta_rpow_mul_nat_half_rpow
    (kappa K : ℝ) {eta : ℝ} (heta : 0 < eta) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C ≤ gamma kappa K N * delta kappa N ^ eta *
        (N : ℝ) ^ (eta / 2) :=
  (tendsto_gamma_mul_delta_rpow_mul_nat_half_rpow_atTop
    kappa K heta).eventually_ge_atTop C

/-- Power-range form of the frozen low-rank growth theorem.  For every fixed
positive retained-population exponent `p`, the source dilation scale remains
unbounded after freezing all logarithmic parameters at the initial card. -/
theorem tendsto_gamma_mul_delta_rpow_mul_nat_rpow_atTop
    (kappa K : ℝ) {eta p : ℝ} (heta : 0 < eta) (hp : 0 < p) :
    Tendsto
      (fun N : ℕ ↦ gamma kappa K N * delta kappa N ^ eta *
        (N : ℝ) ^ (p * eta))
      atTop atTop := by
  have hbase := tendsto_gamma_mul_nat_rpow_atTop
    kappa (K + eta) (mul_pos hp heta)
  apply hbase.congr'
  filter_upwards [eventually_delta_pos kappa] with N hdelta
  unfold gamma
  rw [← Real.rpow_add hdelta]

/-- Fixed-bound form of the arbitrary frozen power-range low-rank growth
theorem. -/
theorem eventually_const_le_gamma_mul_delta_rpow_mul_nat_rpow
    (kappa K : ℝ) {eta p : ℝ} (heta : 0 < eta) (hp : 0 < p)
    (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C ≤ gamma kappa K N * delta kappa N ^ eta *
        (N : ℝ) ^ (p * eta) :=
  (tendsto_gamma_mul_delta_rpow_mul_nat_rpow_atTop
    kappa K heta hp).eventually_ge_atTop C

end

end Erdos186.PZ.Intersection
