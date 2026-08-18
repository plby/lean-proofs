/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFrozenParameterAsymptotics

/-!
# Frozen source growth after a fixed power of the covering parameter
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Any fixed power of the frozen `gamma`, together with the frozen `mu`,
still leaves polynomial room at the square-root terminal population scale. -/
theorem tendsto_gamma_pow_mul_mu_mul_nat_half_rpow_atTop
    (kappa K : ℝ) (p : ℕ) :
    Tendsto (fun N : ℕ ↦
      gamma kappa K N ^ p * mu kappa N * (N : ℝ) ^ (1 / 2 : ℝ))
      atTop atTop := by
  let q : ℝ := 1 / (4 * ((p : ℝ) + 1))
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  apply tendsto_atTop.mpr
  intro C
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      C ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  have hgamma : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-q) ≤ gamma kappa K N :=
    eventually_nat_rpow_neg_le_gamma kappa K hq
  have hmu : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-q) ≤ mu kappa N := by
    simpa only [mu, gamma] using
      eventually_nat_rpow_neg_le_gamma kappa kappa hq
  filter_upwards [hgrowth, hgamma, hmu, eventually_gt_atTop (0 : ℕ)]
    with N hgrowthN hgammaN hmuN hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbase : 0 ≤ (N : ℝ) ^ (-q) := Real.rpow_nonneg hNreal.le _
  have hgammaNonneg : 0 ≤ gamma kappa K N := hbase.trans hgammaN
  have hgammaPow : ((N : ℝ) ^ (-q)) ^ p ≤
      gamma kappa K N ^ p :=
    pow_le_pow_left₀ hbase hgammaN p
  have hexponent : -(q * (p : ℝ)) + -q + 1 / 2 = (1 / 4 : ℝ) := by
    dsimp only [q]
    field_simp
    ring
  calc
    C ≤ (N : ℝ) ^ (1 / 4 : ℝ) := hgrowthN
    _ = (N : ℝ) ^ (-(q * (p : ℝ)) + -q + 1 / 2) := by
      rw [hexponent]
    _ = ((N : ℝ) ^ (-q)) ^ p * (N : ℝ) ^ (-q) *
          (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNreal.le,
        ← Real.rpow_add hNreal, ← Real.rpow_add hNreal]
      congr 1
      ring
    _ ≤ gamma kappa K N ^ p * mu kappa N *
          (N : ℝ) ^ (1 / 2 : ℝ) := by
      gcongr

/-- Eventual fixed-bound form of the frozen covering growth theorem. -/
theorem eventually_const_le_gamma_pow_mul_mu_mul_nat_half_rpow
    (kappa K : ℝ) (p : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C ≤ gamma kappa K N ^ p * mu kappa N *
        (N : ℝ) ^ (1 / 2 : ℝ) :=
  (tendsto_gamma_pow_mul_mu_mul_nat_half_rpow_atTop kappa K p).eventually_ge_atTop C

end

end Erdos186.PZ.Intersection
