/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.IntervalCases

/-!
# Analytic trajectories for the conflict-free matching process

This file contains the deterministic calculus used in the specialization of
the Glock--Joos--Kim--Kuehn--Lichev conflict-free matching process to an
eight-uniform host and conflicts of size at most four.

There is a small but important normalization in these formulas.  If `N` is
the number of host vertices and `d` is the degree scale, then the initial
number of host edges is `d * N / 8`.  Consequently the edge-count trajectory
is

`hHat = (d * N / 8) * q`.

The factor `d` is necessary for all three differential identities below.
-/

namespace Erdos136.CFMTrajectories

open Real Set Filter

noncomputable section

/-- Proportion of uncovered host vertices at continuous time `x`. -/
def pV (N x : ℝ) : ℝ := 1 - 8 * x / N

/-- Heuristic probability that a fixed host edge has entered the matching. -/
def pM (d N x : ℝ) : ℝ := 8 * x / (d * N)

/-- Conflict hazard for conflicts of sizes two, three, and four. -/
def GammaHat (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  D₂ * pM d N x + D₃ * pM d N x ^ 2 + D₄ * pM d N x ^ 3

/-- Survival probability of an auxiliary edge. -/
def q (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  pV N x ^ 8 * exp (-GammaHat D₂ D₃ D₄ d N x)

/-- Trajectory for the number of available auxiliary edges. -/
def hHat (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  d * N / 8 * q D₂ D₃ D₄ d N x

/-- Trajectory for the available degree of a fixed auxiliary vertex. -/
def dHat (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  d * pV N x ^ 7 * exp (-GammaHat D₂ D₃ D₄ d N x)

/-- The `(j,s)` test trajectory. -/
def zHat (D₂ D₃ D₄ d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose j s : ℝ) * q D₂ D₃ D₄ d N x ^ s * pM d N x ^ (j - s)

/-- Expected number of conflicts which are one matching edge away from
forbidding a given available edge. -/
def cHat (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  D₂ * q D₂ D₃ D₄ d N x +
    2 * D₃ * q D₂ D₃ D₄ d N x * pM d N x +
    3 * D₄ * q D₂ D₃ D₄ d N x * pM d N x ^ 2

/-- Relative logarithmic growth rate of the error envelopes.  In the
specialization `k = 8`, `ell = 4`, the source constant
`300 * k^2 * ell` is `76800`. -/
def gamma (Gamma N x : ℝ) : ℝ := 76800 * Gamma / (N * pV N x)

/-- Common multiplicative error factor. -/
def xi (Gamma epsilon d N x : ℝ) : ℝ :=
  (pV N x) ^ (-9600 * Gamma) * d ^ (-epsilon / 32)

/-- Error envelope for an available-vertex degree. -/
def delta (D₂ D₃ D₄ Gamma epsilon d N x : ℝ) : ℝ :=
  xi Gamma epsilon d N x * dHat D₂ D₃ D₄ d N x

/-- Error envelope for a `(j,s)` test variable. -/
def zeta (D₂ D₃ D₄ Gamma epsilon d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  xi Gamma epsilon d N x *
    (zHat D₂ D₃ D₄ d N j s x +
      (Nat.choose j s : ℝ) * dHat D₂ D₃ D₄ d N x ^ s /
        (4 * Gamma * d ^ j))

/-! ## Positivity and elementary parameter relations -/

theorem pV_pos {N x : ℝ} (hN : 0 < N) (hx : 8 * x < N) : 0 < pV N x := by
  rw [pV]
  have : 8 * x / N < 1 := (div_lt_one hN).2 hx
  linarith

theorem pV_nonneg {N x : ℝ} (hN : 0 < N) (hx : 8 * x ≤ N) : 0 ≤ pV N x := by
  rw [pV]
  have : 8 * x / N ≤ 1 := (div_le_one hN).2 hx
  linarith

theorem pV_le_one {N x : ℝ} (hN : 0 < N) (hx : 0 ≤ x) : pV N x ≤ 1 := by
  rw [pV]
  have : 0 ≤ 8 * x / N := by positivity
  linarith

theorem pM_nonneg {d N x : ℝ} (hd : 0 < d) (hN : 0 < N) (hx : 0 ≤ x) :
    0 ≤ pM d N x := by
  unfold pM
  positivity

theorem pM_le_inv {d N x : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hx : 8 * x ≤ N) : pM d N x ≤ d⁻¹ := by
  rw [pM]
  have hden : 0 < d * N := mul_pos hd hN
  calc
    8 * x / (d * N) ≤ N / (d * N) := div_le_div_of_nonneg_right hx hden.le
    _ = d⁻¹ := by field_simp

theorem GammaHat_nonneg {D₂ D₃ D₄ d N x : ℝ}
    (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃) (hD₄ : 0 ≤ D₄)
    (hpM : 0 ≤ pM d N x) : 0 ≤ GammaHat D₂ D₃ D₄ d N x := by
  unfold GammaHat
  positivity

theorem q_pos {D₂ D₃ D₄ d N x : ℝ} (hpV : 0 < pV N x) :
    0 < q D₂ D₃ D₄ d N x := by
  unfold q
  positivity

theorem q_le_one {D₂ D₃ D₄ d N x : ℝ}
    (hpV0 : 0 ≤ pV N x) (hpV1 : pV N x ≤ 1)
    (hGammaHat : 0 ≤ GammaHat D₂ D₃ D₄ d N x) :
    q D₂ D₃ D₄ d N x ≤ 1 := by
  have hpVpow : pV N x ^ 8 ≤ 1 := pow_le_one₀ hpV0 hpV1
  have hexp0 : 0 ≤ exp (-GammaHat D₂ D₃ D₄ d N x) := (Real.exp_pos _).le
  have hexp1 : exp (-GammaHat D₂ D₃ D₄ d N x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  unfold q
  calc
    pV N x ^ 8 * exp (-GammaHat D₂ D₃ D₄ d N x) ≤
        1 * exp (-GammaHat D₂ D₃ D₄ d N x) :=
      mul_le_mul_of_nonneg_right hpVpow hexp0
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hexp1 (by norm_num)
    _ = 1 := by ring

theorem choose_le_six {j s : ℕ} (hsj : s ≤ j) (hj : j ≤ 4) :
    j.choose s ≤ 6 := by
  interval_cases j <;> interval_cases s <;> norm_num [Nat.choose] at *

/-- Conversion between the natural power of the inverse degree and the
real-power scale used in the trajectory statements. -/
theorem inv_pow_eq_rpow_sub {d : ℝ} (hd : 0 < d) {j s : ℕ} (hsj : s ≤ j) :
    (d⁻¹ : ℝ) ^ (j - s) = d ^ ((s : ℝ) - j) := by
  calc
    (d⁻¹ : ℝ) ^ (j - s) = (d⁻¹ : ℝ) ^ ((j - s : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ = (d ^ ((j - s : ℕ) : ℝ))⁻¹ := Real.inv_rpow hd.le _
    _ = d ^ (-((j - s : ℕ) : ℝ)) := (Real.rpow_neg hd.le _).symm
    _ = d ^ ((s : ℝ) - j) := by
      congr 1
      rw [Nat.cast_sub hsj]
      ring

theorem hHat_pos {D₂ D₃ D₄ d N x : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hpV : 0 < pV N x) : 0 < hHat D₂ D₃ D₄ d N x := by
  unfold hHat
  exact mul_pos (div_pos (mul_pos hd hN) (by norm_num)) (q_pos hpV)

theorem dHat_pos {D₂ D₃ D₄ d N x : ℝ} (hd : 0 < d) (hpV : 0 < pV N x) :
    0 < dHat D₂ D₃ D₄ d N x := by
  unfold dHat
  positivity

theorem xi_pos {Gamma epsilon d N x : ℝ} (hd : 0 < d) (hpV : 0 < pV N x) :
    0 < xi Gamma epsilon d N x := by
  unfold xi
  exact mul_pos (Real.rpow_pos_of_pos hpV _) (Real.rpow_pos_of_pos hd _)

theorem delta_pos {D₂ D₃ D₄ Gamma epsilon d N x : ℝ}
    (hd : 0 < d) (hpV : 0 < pV N x) :
    0 < delta D₂ D₃ D₄ Gamma epsilon d N x := by
  exact mul_pos (xi_pos hd hpV) (dHat_pos hd hpV)

theorem zeta_pos {D₂ D₃ D₄ Gamma epsilon d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hGamma : 0 < Gamma) (hpV : 0 < pV N x)
    (hpM : 0 ≤ pM d N x) (hsj : s ≤ j) :
    0 < zeta D₂ D₃ D₄ Gamma epsilon d N j s x := by
  have hchoose : 0 < (Nat.choose j s : ℝ) := by
    exact_mod_cast Nat.choose_pos hsj
  have hdHat : 0 < dHat D₂ D₃ D₄ d N x := dHat_pos hd hpV
  unfold zeta
  apply mul_pos (xi_pos hd hpV)
  apply add_pos_of_nonneg_of_pos
  · unfold zHat
    exact mul_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (q_pos hpV).le _)) (pow_nonneg hpM _)
  · positivity

/-! ## Exact differential identities -/

theorem hasDerivAt_pV (N x : ℝ) : HasDerivAt (pV N) (-8 / N) x := by
  have h := (hasDerivAt_const x 1).sub
    (((hasDerivAt_id x).mul_const 8).div_const N)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [pV]
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · ring

theorem hasDerivAt_pM (d N x : ℝ) : HasDerivAt (pM d N) (8 / (d * N)) x := by
  have h := ((hasDerivAt_id x).mul_const 8).div_const (d * N)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [pM]
    simp only [Pi.mul_apply, id_eq]
    ring
  · ring

theorem hasDerivAt_GammaHat (D₂ D₃ D₄ d N x : ℝ) :
    HasDerivAt (GammaHat D₂ D₃ D₄ d N)
      (8 / (d * N) *
        (D₂ + 2 * D₃ * pM d N x + 3 * D₄ * pM d N x ^ 2)) x := by
  change HasDerivAt
    (fun y => D₂ * pM d N y + D₃ * pM d N y ^ 2 + D₄ * pM d N y ^ 3) _ x
  have h :=
    (((hasDerivAt_pM d N x).mul_const D₂).add
      (((hasDerivAt_pM d N x).pow 2).mul_const D₃)).add
      (((hasDerivAt_pM d N x).pow 3).mul_const D₄)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · norm_num
    ring

theorem hasDerivAt_q (D₂ D₃ D₄ d N x : ℝ) :
    HasDerivAt (q D₂ D₃ D₄ d N)
      ((8 * pV N x ^ 7 * (-8 / N) -
          pV N x ^ 8 *
            (8 / (d * N) *
              (D₂ + 2 * D₃ * pM d N x + 3 * D₄ * pM d N x ^ 2))) *
        exp (-GammaHat D₂ D₃ D₄ d N x)) x := by
  change HasDerivAt
    (fun y => pV N y ^ 8 * exp (-GammaHat D₂ D₃ D₄ d N y)) _ x
  have h :=
    ((hasDerivAt_pV N x).pow 8).mul
      ((hasDerivAt_GammaHat D₂ D₃ D₄ d N x).neg.exp)
  refine h.congr_deriv ?_
  norm_num
  ring

theorem cHat_div_hHat {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x =
      8 / (d * N) *
        (D₂ + 2 * D₃ * pM d N x + 3 * D₄ * pM d N x ^ 2) := by
  have hq : q D₂ D₃ D₄ d N x ≠ 0 := ne_of_gt (q_pos hpV)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hN0 : N ≠ 0 := ne_of_gt hN
  unfold cHat hHat
  field_simp

theorem hasDerivAt_GammaHat_eq_cHat_div_hHat
    {D₂ D₃ D₄ d N x : ℝ} (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (GammaHat D₂ D₃ D₄ d N)
      (cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) x := by
  rw [cHat_div_hHat hd hN hpV]
  exact hasDerivAt_GammaHat D₂ D₃ D₄ d N x

theorem dHat_div_hHat {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x =
      8 / (N * pV N x) := by
  have hq : q D₂ D₃ D₄ d N x ≠ 0 := ne_of_gt (q_pos hpV)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hpV0 : pV N x ≠ 0 := ne_of_gt hpV
  unfold dHat hHat q
  field_simp

theorem hasDerivAt_dHat (D₂ D₃ D₄ d N x : ℝ) :
    HasDerivAt (dHat D₂ D₃ D₄ d N)
      (d *
        (7 * pV N x ^ 6 * (-8 / N) * exp (-GammaHat D₂ D₃ D₄ d N x) -
          pV N x ^ 7 *
            (8 / (d * N) *
              (D₂ + 2 * D₃ * pM d N x + 3 * D₄ * pM d N x ^ 2)) *
            exp (-GammaHat D₂ D₃ D₄ d N x))) x := by
  have h :=
    (((hasDerivAt_pV N x).pow 7).mul
      ((hasDerivAt_GammaHat D₂ D₃ D₄ d N x).neg.exp)).const_mul d
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [dHat, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, id_eq]
    ring
  · norm_num
    ring_nf
    simp

theorem hasDerivAt_dHat_eq
    {D₂ D₃ D₄ d N x : ℝ} (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (dHat D₂ D₃ D₄ d N)
      (-((cHat D₂ D₃ D₄ d N x + 7 * dHat D₂ D₃ D₄ d N x) *
        dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x)) x := by
  rw [show
      -((cHat D₂ D₃ D₄ d N x + 7 * dHat D₂ D₃ D₄ d N x) *
          dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) =
        d *
          (7 * pV N x ^ 6 * (-8 / N) * exp (-GammaHat D₂ D₃ D₄ d N x) -
            pV N x ^ 7 *
              (8 / (d * N) *
                (D₂ + 2 * D₃ * pM d N x + 3 * D₄ * pM d N x ^ 2)) *
              exp (-GammaHat D₂ D₃ D₄ d N x)) by
  have hh : hHat D₂ D₃ D₄ d N x ≠ 0 := ne_of_gt (hHat_pos hd hN hpV)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hpV0 : pV N x ≠ 0 := ne_of_gt hpV
  unfold cHat hHat dHat q
  field_simp
  ring]
  exact hasDerivAt_dHat D₂ D₃ D₄ d N x

theorem hasDerivAt_q_eq
    {D₂ D₃ D₄ d N x : ℝ} (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (q D₂ D₃ D₄ d N)
      (-((cHat D₂ D₃ D₄ d N x + 8 * dHat D₂ D₃ D₄ d N x) *
        q D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x)) x := by
  rw [show
      -((cHat D₂ D₃ D₄ d N x + 8 * dHat D₂ D₃ D₄ d N x) *
          q D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) =
        (8 * pV N x ^ 7 * (-8 / N) -
            pV N x ^ 8 *
              (8 / (d * N) *
                (D₂ + 2 * D₃ * pM d N x + 3 * D₄ * pM d N x ^ 2))) *
          exp (-GammaHat D₂ D₃ D₄ d N x) by
  have hh : hHat D₂ D₃ D₄ d N x ≠ 0 := ne_of_gt (hHat_pos hd hN hpV)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hpV0 : pV N x ≠ 0 := ne_of_gt hpV
  unfold cHat hHat q dHat
  field_simp
  ring]
  exact hasDerivAt_q D₂ D₃ D₄ d N x

theorem hasDerivAt_hHat_eq
    {D₂ D₃ D₄ d N x : ℝ} (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (hHat D₂ D₃ D₄ d N)
      (-(cHat D₂ D₃ D₄ d N x + 8 * dHat D₂ D₃ D₄ d N x)) x := by
  have hraw := (hasDerivAt_q D₂ D₃ D₄ d N x).const_mul (d * N / 8)
  change HasDerivAt (fun y => d * N / 8 * q D₂ D₃ D₄ d N y)
    (-(cHat D₂ D₃ D₄ d N x + 8 * dHat D₂ D₃ D₄ d N x)) x
  rw [show -(cHat D₂ D₃ D₄ d N x + 8 * dHat D₂ D₃ D₄ d N x) =
      (d * N / 8) * ((8 * pV N x ^ 7 * (-8 / N) -
          pV N x ^ 8 *
            (8 / (d * N) *
              (D₂ + 2 * D₃ * pM d N x + 3 * D₄ * pM d N x ^ 2))) *
        exp (-GammaHat D₂ D₃ D₄ d N x)) by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hpV0 : pV N x ≠ 0 := ne_of_gt hpV
  unfold cHat q dHat
  field_simp
  ring]
  exact hraw

theorem hasDerivAt_xi {Gamma epsilon d N x : ℝ}
    (hd : 0 < d) (hpV : 0 < pV N x) :
    HasDerivAt (xi Gamma epsilon d N)
      (gamma Gamma N x * xi Gamma epsilon d N x) x := by
  unfold xi gamma
  have hpV0 : pV N x ≠ 0 := ne_of_gt hpV
  have hraw := ((hasDerivAt_pV N x).rpow_const (p := -9600 * Gamma)
    (Or.inl hpV0)).mul_const
    (d ^ (-epsilon / 32))
  have heq :
      76800 * Gamma / (N * pV N x) *
          (pV N x ^ (-9600 * Gamma) * d ^ (-epsilon / 32)) =
        (-8 / N) * (-9600 * Gamma) *
          pV N x ^ (-9600 * Gamma - 1) * d ^ (-epsilon / 32) := by
    rw [Real.rpow_sub_one hpV0]
    field_simp
    ring
  rw [heq]
  exact hraw

theorem hasDerivAt_delta
    {D₂ D₃ D₄ Gamma epsilon d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (delta D₂ D₃ D₄ Gamma epsilon d N)
      ((gamma Gamma N x - cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x -
          7 * dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
        delta D₂ D₃ D₄ Gamma epsilon d N x) x := by
  unfold delta
  have hraw :=
    (hasDerivAt_xi (Gamma := Gamma) (epsilon := epsilon) hd hpV).mul
      (hasDerivAt_dHat_eq (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV)
  have hraw' : HasDerivAt
      (fun y => xi Gamma epsilon d N y * dHat D₂ D₃ D₄ d N y)
      (gamma Gamma N x * xi Gamma epsilon d N x * dHat D₂ D₃ D₄ d N x +
        xi Gamma epsilon d N x *
          -((cHat D₂ D₃ D₄ d N x + 7 * dHat D₂ D₃ D₄ d N x) *
            dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x)) x := by
    exact hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)
  rw [show
      (gamma Gamma N x - cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x -
          7 * dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
          (xi Gamma epsilon d N x * dHat D₂ D₃ D₄ d N x) =
        gamma Gamma N x * xi Gamma epsilon d N x * dHat D₂ D₃ D₄ d N x +
          xi Gamma epsilon d N x *
            -((cHat D₂ D₃ D₄ d N x + 7 * dHat D₂ D₃ D₄ d N x) *
              dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) by ring]
  exact hraw'

/-! ## Test trajectories and envelopes -/

/-- Raw product-rule form of the derivative of a test trajectory. -/
theorem hasDerivAt_zHat_raw {D₂ D₃ D₄ d N x : ℝ} (j s : ℕ)
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (zHat D₂ D₃ D₄ d N j s)
      ((Nat.choose j s : ℝ) *
        (s * q D₂ D₃ D₄ d N x ^ (s - 1) *
            (-((cHat D₂ D₃ D₄ d N x + 8 * dHat D₂ D₃ D₄ d N x) *
              q D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x)) *
            pM d N x ^ (j - s) +
          q D₂ D₃ D₄ d N x ^ s *
            (((j - s : ℕ) : ℝ) * pM d N x ^ (j - s - 1) * (8 / (d * N))))) x := by
  have h :=
    (((hasDerivAt_q_eq (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV).pow s).mul
      ((hasDerivAt_pM d N x).pow (j - s))).const_mul (Nat.choose j s : ℝ)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [zHat, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [Pi.mul_apply, Pi.pow_apply]

/-- Exact test-trajectory differential identity from the conflict-free
matching process.  Only `j ≤ 4` is needed in the present specialization;
keeping that finite bound here lets Lean verify all boundary cases
(`s = 0` and `s = j`) without division by a binomial coefficient. -/
theorem hasDerivAt_zHat {D₂ D₃ D₄ d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    HasDerivAt (zHat D₂ D₃ D₄ d N j s)
      (((s + 1 : ℕ) : ℝ) * zHat D₂ D₃ D₄ d N j (s + 1) x /
          hHat D₂ D₃ D₄ d N x -
        (s : ℝ) * (cHat D₂ D₃ D₄ d N x + 8 * dHat D₂ D₃ D₄ d N x) *
          zHat D₂ D₃ D₄ d N j s x / hHat D₂ D₃ D₄ d N x) x := by
  have hraw := hasDerivAt_zHat_raw (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    j s hd hN hpV
  refine hraw.congr_deriv ?_
  have hh : hHat D₂ D₃ D₄ d N x ≠ 0 := ne_of_gt (hHat_pos hd hN hpV)
  have hq : q D₂ D₃ D₄ d N x ≠ 0 := ne_of_gt (q_pos hpV)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hN0 : N ≠ 0 := ne_of_gt hN
  interval_cases j <;> interval_cases s <;>
    simp_all only [zHat, hHat, Nat.choose, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
      Nat.zero_sub, Nat.succ_sub_succ_eq_sub, pow_zero, pow_one, zero_mul, one_mul,
      mul_zero, mul_one, zero_add, add_zero] <;>
    field_simp <;> ring

/-- Exact derivative of the test error envelope. -/
theorem hasDerivAt_zeta {D₂ D₃ D₄ Gamma epsilon d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 < Gamma)
    (hpV : 0 < pV N x) (hsj : s ≤ j) (hj : j ≤ 4) :
    HasDerivAt (zeta D₂ D₃ D₄ Gamma epsilon d N j s)
      ((gamma Gamma N x -
          (s : ℝ) * cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x -
          8 * (s : ℝ) * dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
          zeta D₂ D₃ D₄ Gamma epsilon d N j s x +
        ((s + 1 : ℕ) : ℝ) * xi Gamma epsilon d N x *
          zHat D₂ D₃ D₄ d N j (s + 1) x / hHat D₂ D₃ D₄ d N x +
        (s : ℝ) * (Nat.choose j s : ℝ) * xi Gamma epsilon d N x *
          dHat D₂ D₃ D₄ d N x ^ (s + 1) /
            (4 * Gamma * d ^ j * hHat D₂ D₃ D₄ d N x)) x := by
  let aux : ℝ → ℝ := fun y =>
    (Nat.choose j s : ℝ) * dHat D₂ D₃ D₄ d N y ^ s / (4 * Gamma * d ^ j)
  have haux : HasDerivAt aux
      ((Nat.choose j s : ℝ) *
        (s * dHat D₂ D₃ D₄ d N x ^ (s - 1) *
          (-((cHat D₂ D₃ D₄ d N x + 7 * dHat D₂ D₃ D₄ d N x) *
            dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x))) /
        (4 * Gamma * d ^ j)) x := by
    dsimp [aux]
    simpa only [Pi.mul_apply, Pi.pow_apply] using
      (((hasDerivAt_dHat_eq hd hN hpV).pow s).const_mul (Nat.choose j s : ℝ)).div_const
        (4 * Gamma * d ^ j)
  have hsum :=
    (hasDerivAt_zHat (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV hsj hj).add haux
  have hprod :=
    (hasDerivAt_xi (Gamma := Gamma) (epsilon := epsilon) hd hpV).mul hsum
  refine (hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [zeta, aux, Pi.add_apply, Pi.mul_apply]
  · have hh : hHat D₂ D₃ D₄ d N x ≠ 0 := ne_of_gt (hHat_pos hd hN hpV)
    have hd0 : d ≠ 0 := ne_of_gt hd
    have hG0 : Gamma ≠ 0 := ne_of_gt hGamma
    cases s with
    | zero =>
        simp only [zeta, aux, Nat.cast_zero, Nat.choose_zero_right, pow_zero,
          zero_mul, zero_add, one_mul, mul_one, Pi.add_apply, Pi.mul_apply]
        field_simp
        ring
    | succ s =>
        simp only [zeta, aux, Nat.cast_succ, Nat.succ_sub_one, pow_succ,
          Pi.add_apply, Pi.mul_apply]
        field_simp
        ring

/-- Named right-hand side of the exact `zHat` differential equation. -/
def zHatRate (D₂ D₃ D₄ d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  ((s + 1 : ℕ) : ℝ) * zHat D₂ D₃ D₄ d N j (s + 1) x /
      hHat D₂ D₃ D₄ d N x -
    (s : ℝ) * (cHat D₂ D₃ D₄ d N x + 8 * dHat D₂ D₃ D₄ d N x) *
      zHat D₂ D₃ D₄ d N j s x / hHat D₂ D₃ D₄ d N x

/-- Named right-hand side of the exact `zeta` differential equation. -/
def zetaRate (D₂ D₃ D₄ Gamma epsilon d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  (gamma Gamma N x -
      (s : ℝ) * cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x -
      8 * (s : ℝ) * dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
      zeta D₂ D₃ D₄ Gamma epsilon d N j s x +
    ((s + 1 : ℕ) : ℝ) * xi Gamma epsilon d N x *
      zHat D₂ D₃ D₄ d N j (s + 1) x / hHat D₂ D₃ D₄ d N x +
    (s : ℝ) * (Nat.choose j s : ℝ) * xi Gamma epsilon d N x *
      dHat D₂ D₃ D₄ d N x ^ (s + 1) /
        (4 * Gamma * d ^ j * hHat D₂ D₃ D₄ d N x)

/-- Actual second derivative of a test trajectory, defined from its
displayed first-order right-hand side. -/
def zHatCurvature (D₂ D₃ D₄ d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  deriv (zHatRate D₂ D₃ D₄ d N j s) x

/-- Actual second derivative of a test error envelope. -/
def zetaCurvature (D₂ D₃ D₄ Gamma epsilon d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  deriv (zetaRate D₂ D₃ D₄ Gamma epsilon d N j s) x

theorem hasDerivAt_zHat_rate {D₂ D₃ D₄ d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    HasDerivAt (zHat D₂ D₃ D₄ d N j s) (zHatRate D₂ D₃ D₄ d N j s x) x := by
  exact hasDerivAt_zHat hd hN hpV hsj hj

theorem hasDerivAt_zeta_rate {D₂ D₃ D₄ Gamma epsilon d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 < Gamma)
    (hpV : 0 < pV N x) (hsj : s ≤ j) (hj : j ≤ 4) :
    HasDerivAt (zeta D₂ D₃ D₄ Gamma epsilon d N j s)
      (zetaRate D₂ D₃ D₄ Gamma epsilon d N j s x) x := by
  exact hasDerivAt_zeta hd hN hGamma hpV hsj hj

theorem hasDerivAt_zHatRate {D₂ D₃ D₄ d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (zHatRate D₂ D₃ D₄ d N j s)
      (zHatCurvature D₂ D₃ D₄ d N j s x) x := by
  have hh : hHat D₂ D₃ D₄ d N x ≠ 0 := ne_of_gt (hHat_pos hd hN hpV)
  have hz (a b : ℕ) : DifferentiableAt ℝ (zHat D₂ D₃ D₄ d N a b) x := by
    unfold zHat q GammaHat pM pV
    fun_prop
  have hhDiff : DifferentiableAt ℝ (hHat D₂ D₃ D₄ d N) x :=
    (hasDerivAt_hHat_eq hd hN hpV).differentiableAt
  have hdDiff : DifferentiableAt ℝ (dHat D₂ D₃ D₄ d N) x :=
    (hasDerivAt_dHat_eq hd hN hpV).differentiableAt
  have hcDiff : DifferentiableAt ℝ (cHat D₂ D₃ D₄ d N) x := by
    unfold cHat q GammaHat pM pV
    fun_prop
  apply DifferentiableAt.hasDerivAt
  unfold zHatRate
  fun_prop (disch := aesop)

theorem hasDerivAt_zetaRate {D₂ D₃ D₄ Gamma epsilon d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 < Gamma)
    (hpV : 0 < pV N x) :
    HasDerivAt (zetaRate D₂ D₃ D₄ Gamma epsilon d N j s)
      (zetaCurvature D₂ D₃ D₄ Gamma epsilon d N j s x) x := by
  have hh : hHat D₂ D₃ D₄ d N x ≠ 0 := ne_of_gt (hHat_pos hd hN hpV)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hGamma0 : Gamma ≠ 0 := ne_of_gt hGamma
  have hpV0 : pV N x ≠ 0 := ne_of_gt hpV
  have hz (a b : ℕ) : DifferentiableAt ℝ (zHat D₂ D₃ D₄ d N a b) x := by
    unfold zHat q GammaHat pM pV
    fun_prop
  have hhDiff : DifferentiableAt ℝ (hHat D₂ D₃ D₄ d N) x :=
    (hasDerivAt_hHat_eq hd hN hpV).differentiableAt
  have hdDiff : DifferentiableAt ℝ (dHat D₂ D₃ D₄ d N) x :=
    (hasDerivAt_dHat_eq hd hN hpV).differentiableAt
  have hcDiff : DifferentiableAt ℝ (cHat D₂ D₃ D₄ d N) x := by
    unfold cHat q GammaHat pM pV
    fun_prop
  have hxiDiff : DifferentiableAt ℝ (xi Gamma epsilon d N) x :=
    (hasDerivAt_xi hd hpV).differentiableAt
  have hgammaDiff : DifferentiableAt ℝ (gamma Gamma N) x := by
    unfold gamma pV
    fun_prop (disch := aesop)
  have hzetaDiff : DifferentiableAt ℝ (zeta D₂ D₃ D₄ Gamma epsilon d N j s) x := by
    unfold zeta
    fun_prop
  apply DifferentiableAt.hasDerivAt
  unfold zetaRate
  fun_prop (disch := aesop)

/-! ## Parameter bounds -/

/-- The normalized conflict load which occurs in `GammaHat'`. -/
def conflictLoad (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  D₂ + 2 * D₃ * pM d N x + 3 * D₄ * pM d N x ^ 2

theorem conflictLoad_nonneg {D₂ D₃ D₄ d N x : ℝ}
    (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃) (hD₄ : 0 ≤ D₄)
    (hpM : 0 ≤ pM d N x) : 0 ≤ conflictLoad D₂ D₃ D₄ d N x := by
  unfold conflictLoad
  positivity

/-- The source codegree hypotheses imply the uniform normalized conflict
load bound used in the differential-equation argument. -/
theorem conflictLoad_le_six_mul {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    conflictLoad D₂ D₃ D₄ d N x ≤ 6 * Gamma * d := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hpd0 : 0 ≤ d * pM d N x := mul_nonneg hd.le hpM0
  have hpd1 : d * pM d N x ≤ 1 := by
    calc
      d * pM d N x ≤ d * d⁻¹ := mul_le_mul_of_nonneg_left hpM1 hd.le
      _ = 1 := mul_inv_cancel₀ hd0
  have hpdsq : (d * pM d N x) ^ 2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self hpd0 hpd1]
  have hD₃p : D₃ * pM d N x ≤ Gamma * d := by
    calc
      D₃ * pM d N x ≤ (Gamma * d ^ 2) * pM d N x :=
        mul_le_mul_of_nonneg_right hD₃ hpM0
      _ = (Gamma * d) * (d * pM d N x) := by ring
      _ ≤ (Gamma * d) * 1 :=
        mul_le_mul_of_nonneg_left hpd1 (mul_nonneg hGamma hd.le)
      _ = Gamma * d := by ring
  have hD₄p : D₄ * pM d N x ^ 2 ≤ Gamma * d := by
    calc
      D₄ * pM d N x ^ 2 ≤ (Gamma * d ^ 3) * pM d N x ^ 2 :=
        mul_le_mul_of_nonneg_right hD₄ (sq_nonneg _)
      _ = (Gamma * d) * (d * pM d N x) ^ 2 := by ring
      _ ≤ (Gamma * d) * 1 :=
        mul_le_mul_of_nonneg_left hpdsq (mul_nonneg hGamma hd.le)
      _ = Gamma * d := by ring
  unfold conflictLoad
  linarith

/-- The corresponding conflict hazard is at most `3 * Gamma`. -/
theorem GammaHat_le_three_mul {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃) (hD₄ : 0 ≤ D₄)
    (hD₂' : D₂ ≤ Gamma * d) (hD₃' : D₃ ≤ Gamma * d ^ 2)
    (hD₄' : D₄ ≤ Gamma * d ^ 3) :
    GammaHat D₂ D₃ D₄ d N x ≤ 3 * Gamma := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hpd0 : 0 ≤ d * pM d N x := mul_nonneg hd.le hpM0
  have hpd1 : d * pM d N x ≤ 1 := by
    calc
      d * pM d N x ≤ d * d⁻¹ := mul_le_mul_of_nonneg_left hpM1 hd.le
      _ = 1 := mul_inv_cancel₀ hd0
  have hpdsq : (d * pM d N x) ^ 2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self hpd0 hpd1]
  have hpdcu : (d * pM d N x) ^ 3 ≤ 1 := by
    calc
      (d * pM d N x) ^ 3 = (d * pM d N x) ^ 2 * (d * pM d N x) := by ring
      _ ≤ 1 * 1 := mul_le_mul hpdsq hpd1 hpd0 (by norm_num)
      _ = 1 := by norm_num
  have h₂ : D₂ * pM d N x ≤ Gamma := by
    calc
      D₂ * pM d N x ≤ (Gamma * d) * pM d N x :=
        mul_le_mul_of_nonneg_right hD₂' hpM0
      _ = Gamma * (d * pM d N x) := by ring
      _ ≤ Gamma * 1 := mul_le_mul_of_nonneg_left hpd1 hGamma
      _ = Gamma := by ring
  have h₃ : D₃ * pM d N x ^ 2 ≤ Gamma := by
    calc
      D₃ * pM d N x ^ 2 ≤ (Gamma * d ^ 2) * pM d N x ^ 2 :=
        mul_le_mul_of_nonneg_right hD₃' (sq_nonneg _)
      _ = Gamma * (d * pM d N x) ^ 2 := by ring
      _ ≤ Gamma * 1 := mul_le_mul_of_nonneg_left hpdsq hGamma
      _ = Gamma := by ring
  have h₄ : D₄ * pM d N x ^ 3 ≤ Gamma := by
    calc
      D₄ * pM d N x ^ 3 ≤ (Gamma * d ^ 3) * pM d N x ^ 3 :=
        mul_le_mul_of_nonneg_right hD₄' (pow_nonneg hpM0 _)
      _ = Gamma * (d * pM d N x) ^ 3 := by ring
      _ ≤ Gamma * 1 := mul_le_mul_of_nonneg_left hpdcu hGamma
      _ = Gamma := by ring
  unfold GammaHat
  linarith

/-- The conflict contribution to the logarithmic drift is uniformly small. -/
theorem cHat_div_hHat_le {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 ≤ Gamma)
    (hpV : 0 < pV N x) (hpM0 : 0 ≤ pM d N x)
    (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x ≤ 48 * Gamma / N := by
  rw [cHat_div_hHat hd hN hpV]
  have hload := conflictLoad_le_six_mul hd hGamma hpM0 hpM1 hD₂ hD₃ hD₄
  change 8 / (d * N) * conflictLoad D₂ D₃ D₄ d N x ≤ _
  calc
    8 / (d * N) * conflictLoad D₂ D₃ D₄ d N x ≤
        8 / (d * N) * (6 * Gamma * d) :=
      mul_le_mul_of_nonneg_left hload (by positivity)
    _ = 48 * Gamma / N := by field_simp; ring

/-- Multiplicative form of the degree-envelope bounds.  This lemma is used
after the process-specific estimates on `xi` and `dHat` have been proved. -/
theorem delta_bounds {D₂ D₃ D₄ Gamma epsilon d N x : ℝ}
    (hd : 0 < d)
    (hxiLower : d ^ (-epsilon / 32) ≤ xi Gamma epsilon d N x)
    (hdLower : d ^ (1 - epsilon / 32) ≤ dHat D₂ D₃ D₄ d N x)
    (hxiUpper : xi Gamma epsilon d N x ≤ d ^ (epsilon / 128))
    (hdUpper : dHat D₂ D₃ D₄ d N x ≤ d ^ (1 - epsilon / 128)) :
    d ^ (1 - epsilon / 16) ≤ delta D₂ D₃ D₄ Gamma epsilon d N x ∧
      delta D₂ D₃ D₄ Gamma epsilon d N x ≤ d := by
  constructor
  · unfold delta
    have hpow1 : 0 ≤ d ^ (-epsilon / 32) := Real.rpow_nonneg hd.le _
    have hpow2 : 0 ≤ d ^ (1 - epsilon / 32) := Real.rpow_nonneg hd.le _
    have hxi0 : 0 ≤ xi Gamma epsilon d N x := hpow1.trans hxiLower
    calc
      d ^ (1 - epsilon / 16) = d ^ (-epsilon / 32) * d ^ (1 - epsilon / 32) := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
      _ ≤ xi Gamma epsilon d N x * dHat D₂ D₃ D₄ d N x :=
        mul_le_mul hxiLower hdLower hpow2 hxi0
  · unfold delta
    have hxi0 : 0 ≤ xi Gamma epsilon d N x :=
      (Real.rpow_nonneg hd.le (-epsilon / 32)).trans hxiLower
    have hdHat0 : 0 ≤ dHat D₂ D₃ D₄ d N x :=
      (Real.rpow_nonneg hd.le (1 - epsilon / 32)).trans hdLower
    have hxiPower0 : 0 ≤ d ^ (epsilon / 128) := Real.rpow_nonneg hd.le _
    calc
      xi Gamma epsilon d N x * dHat D₂ D₃ D₄ d N x ≤
          d ^ (epsilon / 128) * d ^ (1 - epsilon / 128) :=
        mul_le_mul hxiUpper hdUpper hdHat0 hxiPower0
      _ = d := by
        rw [← Real.rpow_add hd]
        convert Real.rpow_one d using 1 <;> ring_nf

/-- The exact source exponents for the degree envelope. -/
theorem delta_bounds_exact {D₂ D₃ D₄ Gamma epsilon d N x : ℝ}
    (hd : 0 < d) (hpV : 0 < pV N x)
    (hxiLower : d ^ (-epsilon / 32) ≤ xi Gamma epsilon d N x)
    (hdLower : d ^ (1 - epsilon / 32) ≤ dHat D₂ D₃ D₄ d N x)
    (hxiUpper : xi Gamma epsilon d N x ≤ d ^ (-epsilon / 64))
    (hdUpper : dHat D₂ D₃ D₄ d N x ≤ d) :
    d ^ (1 - epsilon / 16) ≤ delta D₂ D₃ D₄ Gamma epsilon d N x ∧
      delta D₂ D₃ D₄ Gamma epsilon d N x ≤ d ^ (1 - epsilon / 64) := by
  have hxi0 : 0 ≤ xi Gamma epsilon d N x := (xi_pos hd hpV).le
  have hdHat0 : 0 ≤ dHat D₂ D₃ D₄ d N x := (dHat_pos hd hpV).le
  constructor
  · unfold delta
    calc
      d ^ (1 - epsilon / 16) =
          d ^ (-epsilon / 32) * d ^ (1 - epsilon / 32) := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
      _ ≤ xi Gamma epsilon d N x * dHat D₂ D₃ D₄ d N x :=
        mul_le_mul hxiLower hdLower (Real.rpow_nonneg hd.le _) hxi0
  · unfold delta
    calc
      xi Gamma epsilon d N x * dHat D₂ D₃ D₄ d N x ≤
          d ^ (-epsilon / 64) * d :=
        mul_le_mul hxiUpper hdUpper hdHat0 (Real.rpow_nonneg hd.le _)
      _ = d ^ (1 - epsilon / 64) := by
        calc
          d ^ (-epsilon / 64) * d = d ^ (-epsilon / 64) * d ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = d ^ (-epsilon / 64 + 1) := by rw [Real.rpow_add hd]
          _ = d ^ (1 - epsilon / 64) := by congr 1 <;> ring

/-! ## Derivative margins and one-step estimates -/

/-- The specialized source constant leaves a large positive logarithmic
margin over the geometric degree drift. -/
theorem gamma_sub_geometric_margin {Gamma N x : ℝ}
    (hGamma : 1 ≤ Gamma) (hN : 0 < N) (hpV : 0 < pV N x) :
    76000 * Gamma / (N * pV N x) ≤
      gamma Gamma N x - 56 / (N * pV N x) := by
  unfold gamma
  have hden : 0 < N * pV N x := mul_pos hN hpV
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (by nlinarith) hden.le

/-- Exact degree-envelope margin after both the conflict and geometric
losses are subtracted.  The assumptions are precisely the specialized
source codegree bounds. -/
theorem delta_logarithmic_margin {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hx0 : 0 ≤ x) (hx1 : 8 * x < N)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    76000 * Gamma / (N * pV N x) ≤
      gamma Gamma N x - cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x -
        7 * dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x := by
  have hpV := pV_pos hN hx1
  have hpV1 := pV_le_one hN hx0
  have hpM0 := pM_nonneg hd hN hx0
  have hpM1 := pM_le_inv hd hN hx1.le
  have hden : 0 < N * pV N x := mul_pos hN hpV
  have hGamma0 : 0 ≤ Gamma := by linarith
  have hc := cHat_div_hHat_le hd hN hGamma0 hpV hpM0 hpM1 hD₂ hD₃ hD₄
  have hc0 : 0 ≤ cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x := by
    apply div_nonneg
    · unfold cHat
      have hq : 0 ≤ q D₂ D₃ D₄ d N x := (q_pos hpV).le
      positivity
    · exact (hHat_pos hd hN hpV).le
  have hcScaled :
      (cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
          (N * pV N x) ≤ 48 * Gamma := by
    calc
      _ ≤ (48 * Gamma / N) * (N * pV N x) :=
        mul_le_mul_of_nonneg_right hc hden.le
      _ = 48 * Gamma * pV N x := by field_simp
      _ ≤ 48 * Gamma * 1 :=
        mul_le_mul_of_nonneg_left hpV1 (by positivity)
      _ = 48 * Gamma := by ring
  have hgeom : 56 ≤ 56 * Gamma := by nlinarith
  apply (div_le_iff₀ hden).2
  rw [gamma, show
    7 * dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x =
      7 * (dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) by ring,
    dHat_div_hHat hd hN hpV]
  have heq :
      (76800 * Gamma / (N * pV N x) -
          cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x -
          7 * (8 / (N * pV N x))) * (N * pV N x) =
        76800 * Gamma -
          (cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
            (N * pV N x) - 56 := by
    field_simp
    ring
  rw [heq]
  linarith

/-- Exact `(j,s)`-test margin.  The worst case is `s = 4`; the numerical
constant `76000` leaves more than the required slack. -/
theorem zeta_logarithmic_margin {D₂ D₃ D₄ Gamma d N x : ℝ} {s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hx0 : 0 ≤ x) (hx1 : 8 * x < N) (hs : s ≤ 4)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    76000 * Gamma / (N * pV N x) ≤
      gamma Gamma N x -
        (s : ℝ) * cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x -
        8 * (s : ℝ) * dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x := by
  have hpV := pV_pos hN hx1
  have hpV1 := pV_le_one hN hx0
  have hpM0 := pM_nonneg hd hN hx0
  have hpM1 := pM_le_inv hd hN hx1.le
  have hden : 0 < N * pV N x := mul_pos hN hpV
  have hGamma0 : 0 ≤ Gamma := by linarith
  have hc := cHat_div_hHat_le hd hN hGamma0 hpV hpM0 hpM1 hD₂ hD₃ hD₄
  have hc0 : 0 ≤ cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x := by
    apply div_nonneg
    · unfold cHat
      have hq : 0 ≤ q D₂ D₃ D₄ d N x := (q_pos hpV).le
      positivity
    · exact (hHat_pos hd hN hpV).le
  have hcScaled0 : 0 ≤
      (cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
        (N * pV N x) := mul_nonneg hc0 hden.le
  have hcScaled :
      (cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
          (N * pV N x) ≤ 48 * Gamma := by
    calc
      _ ≤ (48 * Gamma / N) * (N * pV N x) :=
        mul_le_mul_of_nonneg_right hc hden.le
      _ = 48 * Gamma * pV N x := by field_simp
      _ ≤ 48 * Gamma * 1 :=
        mul_le_mul_of_nonneg_left hpV1 (by positivity)
      _ = 48 * Gamma := by ring
  have hs0 : 0 ≤ (s : ℝ) := by positivity
  have hs4 : (s : ℝ) ≤ 4 := by exact_mod_cast hs
  have hconflict :
      (s : ℝ) *
          ((cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
            (N * pV N x)) ≤ 192 * Gamma := by
    calc
      _ ≤ 4 *
          ((cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
            (N * pV N x)) := mul_le_mul_of_nonneg_right hs4 hcScaled0
      _ ≤ 4 * (48 * Gamma) := mul_le_mul_of_nonneg_left hcScaled (by norm_num)
      _ = 192 * Gamma := by ring
  have hgeom : 64 * (s : ℝ) ≤ 256 * Gamma := by nlinarith
  apply (div_le_iff₀ hden).2
  rw [gamma, show
    8 * (s : ℝ) * dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x =
      8 * (s : ℝ) *
        (dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) by ring,
    dHat_div_hHat hd hN hpV]
  have heq :
      (76800 * Gamma / (N * pV N x) -
          (s : ℝ) * cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x -
          8 * (s : ℝ) * (8 / (N * pV N x))) * (N * pV N x) =
        76800 * Gamma -
          (s : ℝ) *
            ((cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) *
              (N * pV N x)) - 64 * (s : ℝ) := by
    field_simp
    ring
  rw [heq]
  linarith

/-! ## Second derivatives and explicit large-parameter estimates -/

/-- Logarithmic decay rate of the degree trajectory. -/
def degreeHazard (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  8 / (d * N) * conflictLoad D₂ D₃ D₄ d N x + 56 / (N * pV N x)

/-- Derivative of `degreeHazard`. -/
def degreeHazardSlope (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  (8 / (d * N)) ^ 2 * (2 * D₃ + 6 * D₄ * pM d N x) +
    448 / (N ^ 2 * pV N x ^ 2)

/-- First derivative of `dHat`, written as a named trajectory. -/
def degreeRate (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  -degreeHazard D₂ D₃ D₄ d N x * dHat D₂ D₃ D₄ d N x

/-- Second derivative of `dHat`. -/
def degreeCurvature (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  (degreeHazard D₂ D₃ D₄ d N x ^ 2 - degreeHazardSlope D₂ D₃ D₄ d N x) *
    dHat D₂ D₃ D₄ d N x

/-- Derivative of the envelope growth rate `gamma`. -/
def gammaSlope (Gamma N x : ℝ) : ℝ :=
  614400 * Gamma / (N ^ 2 * pV N x ^ 2)

/-- First derivative of the degree error envelope. -/
def deltaRate (D₂ D₃ D₄ Gamma epsilon d N x : ℝ) : ℝ :=
  (gamma Gamma N x - degreeHazard D₂ D₃ D₄ d N x) *
    delta D₂ D₃ D₄ Gamma epsilon d N x

/-- Second derivative of the degree error envelope. -/
def deltaCurvature (D₂ D₃ D₄ Gamma epsilon d N x : ℝ) : ℝ :=
  ((gamma Gamma N x - degreeHazard D₂ D₃ D₄ d N x) ^ 2 +
      gammaSlope Gamma N x - degreeHazardSlope D₂ D₃ D₄ d N x) *
    delta D₂ D₃ D₄ Gamma epsilon d N x

theorem hasDerivAt_conflictLoad (D₂ D₃ D₄ d N x : ℝ) :
    HasDerivAt (conflictLoad D₂ D₃ D₄ d N)
      (8 / (d * N) * (2 * D₃ + 6 * D₄ * pM d N x)) x := by
  change HasDerivAt
    (fun y => D₂ + 2 * D₃ * pM d N y + 3 * D₄ * pM d N y ^ 2) _ x
  have h := ((hasDerivAt_const x D₂).add
    ((hasDerivAt_pM d N x).const_mul (2 * D₃))).add
    (((hasDerivAt_pM d N x).pow 2).const_mul (3 * D₄))
  refine h.congr_deriv ?_
  norm_num
  ring

theorem hasDerivAt_degreeHazard {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (degreeHazard D₂ D₃ D₄ d N)
      (degreeHazardSlope D₂ D₃ D₄ d N x) x := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hpV0 : pV N x ≠ 0 := ne_of_gt hpV
  have hconf := (hasDerivAt_conflictLoad D₂ D₃ D₄ d N x).const_mul (8 / (d * N))
  have hden := ((hasDerivAt_const x N).mul (hasDerivAt_pV N x)).inv
    (mul_ne_zero hN0 hpV0)
  have hgeom := hden.const_mul 56
  have h := hconf.add hgeom
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [degreeHazard, conflictLoad, Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    ring
  · unfold degreeHazardSlope
    simp only [Pi.mul_apply]
    field_simp
    ring

theorem hasDerivAt_dHat_degreeRate {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (dHat D₂ D₃ D₄ d N) (degreeRate D₂ D₃ D₄ d N x) x := by
  have h := hasDerivAt_dHat_eq (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV
  refine h.congr_deriv ?_
  rw [show
    -((cHat D₂ D₃ D₄ d N x + 7 * dHat D₂ D₃ D₄ d N x) *
        dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) =
      -(cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x +
          7 * (dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x)) *
        dHat D₂ D₃ D₄ d N x by
    field_simp]
  rw [cHat_div_hHat hd hN hpV, dHat_div_hHat hd hN hpV]
  unfold degreeRate degreeHazard conflictLoad
  ring

theorem hasDerivAt_degreeRate {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (degreeRate D₂ D₃ D₄ d N)
      (degreeCurvature D₂ D₃ D₄ d N x) x := by
  have h := (hasDerivAt_degreeHazard (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    hd hN hpV).neg.mul
      (hasDerivAt_dHat_degreeRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [degreeRate, Pi.mul_apply, Pi.neg_apply]
  · unfold degreeCurvature degreeRate
    simp only [Pi.neg_apply]
    ring

theorem hasDerivAt_gamma {Gamma N x : ℝ}
    (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (gamma Gamma N) (gammaSlope Gamma N x) x := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hpV0 : pV N x ≠ 0 := ne_of_gt hpV
  have hden := ((hasDerivAt_const x N).mul (hasDerivAt_pV N x)).inv
    (mul_ne_zero hN0 hpV0)
  have h := hden.const_mul (76800 * Gamma)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [gamma, Pi.mul_apply, Pi.inv_apply]
    ring
  · unfold gammaSlope
    simp only [Pi.mul_apply]
    field_simp
    ring

theorem hasDerivAt_delta_rate {D₂ D₃ D₄ Gamma epsilon d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (delta D₂ D₃ D₄ Gamma epsilon d N)
      (deltaRate D₂ D₃ D₄ Gamma epsilon d N x) x := by
  have h := hasDerivAt_delta (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    (Gamma := Gamma) (epsilon := epsilon) hd hN hpV
  refine h.congr_deriv ?_
  unfold deltaRate degreeHazard conflictLoad
  rw [cHat_div_hHat hd hN hpV]
  rw [show
    7 * dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x =
      7 * (dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) by ring,
    dHat_div_hHat hd hN hpV]
  ring

theorem hasDerivAt_deltaRate {D₂ D₃ D₄ Gamma epsilon d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (deltaRate D₂ D₃ D₄ Gamma epsilon d N)
      (deltaCurvature D₂ D₃ D₄ Gamma epsilon d N x) x := by
  have hcoeff := (hasDerivAt_gamma (Gamma := Gamma) hN hpV).sub
    (hasDerivAt_degreeHazard (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV)
  have h := hcoeff.mul
    (hasDerivAt_delta_rate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
      (Gamma := Gamma) (epsilon := epsilon) hd hN hpV)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [deltaRate, Pi.mul_apply, Pi.sub_apply]
  · simp only [Pi.sub_apply]
    unfold deltaCurvature deltaRate
    ring

/-- A degree trajectory never exceeds its initial degree scale while the
vertex proportion lies in `[0,1]` and the conflict hazard is nonnegative. -/
theorem dHat_le_d {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 ≤ d) (hpV0 : 0 ≤ pV N x) (hpV1 : pV N x ≤ 1)
    (hGammaHat : 0 ≤ GammaHat D₂ D₃ D₄ d N x) :
    dHat D₂ D₃ D₄ d N x ≤ d := by
  have hpVpow : pV N x ^ 7 ≤ 1 := pow_le_one₀ hpV0 hpV1
  have hexp0 : 0 ≤ exp (-GammaHat D₂ D₃ D₄ d N x) := (Real.exp_pos _).le
  have hexp1 : exp (-GammaHat D₂ D₃ D₄ d N x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  unfold dHat
  calc
    d * pV N x ^ 7 * exp (-GammaHat D₂ D₃ D₄ d N x) ≤
        d * 1 * exp (-GammaHat D₂ D₃ D₄ d N x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpVpow hd) hexp0
    _ ≤ d * 1 * 1 := mul_le_mul_of_nonneg_left hexp1 (by positivity)
    _ = d := by ring

/-- The derivative of the normalized conflict load has its source-scale
bound. -/
theorem conflictSlope_le_eight_mul {D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₃ : D₃ ≤ Gamma * d ^ 2) (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    2 * D₃ + 6 * D₄ * pM d N x ≤ 8 * Gamma * d ^ 2 := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hpd : d * pM d N x ≤ 1 := by
    calc
      d * pM d N x ≤ d * d⁻¹ := mul_le_mul_of_nonneg_left hpM1 hd.le
      _ = 1 := mul_inv_cancel₀ hd0
  have hD₄p : D₄ * pM d N x ≤ Gamma * d ^ 2 := by
    calc
      D₄ * pM d N x ≤ (Gamma * d ^ 3) * pM d N x :=
        mul_le_mul_of_nonneg_right hD₄ hpM0
      _ = (Gamma * d ^ 2) * (d * pM d N x) := by ring
      _ ≤ (Gamma * d ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hpd (mul_nonneg hGamma (sq_nonneg d))
      _ = Gamma * d ^ 2 := by ring
  linarith

theorem degreeHazard_nonneg {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x)
    (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃) (hD₄ : 0 ≤ D₄)
    (hpM : 0 ≤ pM d N x) : 0 ≤ degreeHazard D₂ D₃ D₄ d N x := by
  unfold degreeHazard
  have hload := conflictLoad_nonneg hD₂ hD₃ hD₄ hpM
  positivity

theorem degreeHazard_le {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N x) (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    degreeHazard D₂ D₃ D₄ d N x ≤
      104 * Gamma / (N * pV N x) := by
  have hGamma0 : 0 ≤ Gamma := by linarith
  have hload := conflictLoad_le_six_mul hd hGamma0 hpM0 hpM1 hD₂ hD₃ hD₄
  have hden : 0 < N * pV N x := mul_pos hN hpV
  have hconf :
      8 / (d * N) * conflictLoad D₂ D₃ D₄ d N x ≤
        48 * Gamma / (N * pV N x) := by
    apply (le_div_iff₀ hden).2
    calc
      (8 / (d * N) * conflictLoad D₂ D₃ D₄ d N x) * (N * pV N x) ≤
          (8 / (d * N) * (6 * Gamma * d)) * (N * pV N x) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hload (by positivity)) hden.le
      _ = 48 * Gamma * pV N x := by field_simp; ring
      _ ≤ 48 * Gamma * 1 :=
        mul_le_mul_of_nonneg_left hpV1 (by positivity)
      _ = 48 * Gamma := by ring
  have hgeom : 56 / (N * pV N x) ≤ 56 * Gamma / (N * pV N x) := by
    exact div_le_div_of_nonneg_right (by nlinarith) hden.le
  unfold degreeHazard
  calc
    8 / (d * N) * conflictLoad D₂ D₃ D₄ d N x + 56 / (N * pV N x) ≤
        48 * Gamma / (N * pV N x) + 56 * Gamma / (N * pV N x) :=
      add_le_add hconf hgeom
    _ = 104 * Gamma / (N * pV N x) := by ring

theorem degreeHazardSlope_nonneg {D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x)
    (hD₃ : 0 ≤ D₃) (hD₄ : 0 ≤ D₄) (hpM : 0 ≤ pM d N x) :
    0 ≤ degreeHazardSlope (D₂ := (0 : ℝ)) D₃ D₄ d N x := by
  unfold degreeHazardSlope
  positivity

theorem degreeHazardSlope_le {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N x) (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₃ : D₃ ≤ Gamma * d ^ 2) (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    degreeHazardSlope D₂ D₃ D₄ d N x ≤
      960 * Gamma / (N ^ 2 * pV N x ^ 2) := by
  have hGamma0 : 0 ≤ Gamma := by linarith
  have hslope := conflictSlope_le_eight_mul hd hGamma0 hpM0 hpM1 hD₃ hD₄
  have hden2 : 0 < N ^ 2 * pV N x ^ 2 := mul_pos (sq_pos_of_pos hN) (sq_pos_of_pos hpV)
  have hpVsq : pV N x ^ 2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self hpV.le hpV1]
  have hconf :
      (8 / (d * N)) ^ 2 * (2 * D₃ + 6 * D₄ * pM d N x) ≤
        512 * Gamma / (N ^ 2 * pV N x ^ 2) := by
    apply (le_div_iff₀ hden2).2
    calc
      ((8 / (d * N)) ^ 2 * (2 * D₃ + 6 * D₄ * pM d N x)) *
          (N ^ 2 * pV N x ^ 2) ≤
        ((8 / (d * N)) ^ 2 * (8 * Gamma * d ^ 2)) *
          (N ^ 2 * pV N x ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hslope (sq_nonneg _)) hden2.le
      _ = 512 * Gamma * pV N x ^ 2 := by field_simp; ring
      _ ≤ 512 * Gamma * 1 :=
        mul_le_mul_of_nonneg_left hpVsq (by positivity)
      _ = 512 * Gamma := by ring
  have hgeom : 448 / (N ^ 2 * pV N x ^ 2) ≤
      448 * Gamma / (N ^ 2 * pV N x ^ 2) :=
    div_le_div_of_nonneg_right (by nlinarith) hden2.le
  unfold degreeHazardSlope
  calc
    (8 / (d * N)) ^ 2 * (2 * D₃ + 6 * D₄ * pM d N x) +
        448 / (N ^ 2 * pV N x ^ 2) ≤
      512 * Gamma / (N ^ 2 * pV N x ^ 2) +
        448 * Gamma / (N ^ 2 * pV N x ^ 2) := add_le_add hconf hgeom
    _ = 960 * Gamma / (N ^ 2 * pV N x ^ 2) := by ring

/-- Pointwise second-derivative estimate obtained from the displayed
trajectory formulas and the source codegree hypotheses. -/
theorem degreeCurvature_bound {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N x) (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    |degreeCurvature D₂ D₃ D₄ d N x| ≤
      12000 * Gamma ^ 2 * d / (N ^ 2 * pV N x ^ 2) := by
  have hGamma0 : 0 ≤ Gamma := by linarith
  have hA0 := degreeHazard_nonneg hd hN hpV hD₂0 hD₃0 hD₄0 hpM0
  have hA := degreeHazard_le hd hN hGamma hpV hpV1 hpM0 hpM1 hD₂ hD₃ hD₄
  have hS0 : 0 ≤ degreeHazardSlope D₂ D₃ D₄ d N x := by
    unfold degreeHazardSlope
    positivity
  have hS := degreeHazardSlope_le (D₂ := D₂) hd hN hGamma hpV hpV1 hpM0 hpM1 hD₃ hD₄
  have hGH := GammaHat_nonneg hD₂0 hD₃0 hD₄0 hpM0
  have hdHat0 : 0 ≤ dHat D₂ D₃ D₄ d N x := (dHat_pos hd hpV).le
  have hdHat := dHat_le_d hd.le hpV.le hpV1 hGH
  have hden : 0 < N * pV N x := mul_pos hN hpV
  have hden2 : N ^ 2 * pV N x ^ 2 = (N * pV N x) ^ 2 := by ring
  have hAsq : degreeHazard D₂ D₃ D₄ d N x ^ 2 ≤
      (104 * Gamma / (N * pV N x)) ^ 2 := by
    nlinarith [mul_self_le_mul_self hA0 hA]
  have hGsq : Gamma ≤ Gamma ^ 2 := by nlinarith
  have hS' : degreeHazardSlope D₂ D₃ D₄ d N x ≤
      960 * Gamma / (N * pV N x) ^ 2 := by simpa [hden2] using hS
  have hAsq' : degreeHazard D₂ D₃ D₄ d N x ^ 2 ≤
      10816 * Gamma ^ 2 / (N * pV N x) ^ 2 := by
    calc
      _ ≤ (104 * Gamma / (N * pV N x)) ^ 2 := hAsq
      _ = 10816 * Gamma ^ 2 / (N * pV N x) ^ 2 := by ring
  have h960 : 960 * Gamma / (N * pV N x) ^ 2 ≤
      960 * Gamma ^ 2 / (N * pV N x) ^ 2 := by
    exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _)
  have hsum : degreeHazard D₂ D₃ D₄ d N x ^ 2 +
      degreeHazardSlope D₂ D₃ D₄ d N x ≤
        12000 * Gamma ^ 2 / (N * pV N x) ^ 2 := by
    calc
      _ ≤ 10816 * Gamma ^ 2 / (N * pV N x) ^ 2 +
          960 * Gamma / (N * pV N x) ^ 2 := add_le_add hAsq' hS'
      _ ≤ 10816 * Gamma ^ 2 / (N * pV N x) ^ 2 +
          960 * Gamma ^ 2 / (N * pV N x) ^ 2 := add_le_add (le_refl _) h960
      _ = 11776 * Gamma ^ 2 / (N * pV N x) ^ 2 := by ring
      _ ≤ 12000 * Gamma ^ 2 / (N * pV N x) ^ 2 := by
        exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg Gamma]) (sq_nonneg _)
  have hcoef :
      |degreeHazard D₂ D₃ D₄ d N x ^ 2 -
          degreeHazardSlope D₂ D₃ D₄ d N x| ≤
        12000 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) := by
    rw [abs_sub_le_iff]
    constructor
    · rw [hden2]
      nlinarith
    · rw [hden2]
      nlinarith [sq_nonneg (degreeHazard D₂ D₃ D₄ d N x)]
  unfold degreeCurvature
  rw [abs_mul]
  rw [abs_of_nonneg hdHat0]
  have hR0 : 0 ≤ 12000 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) := by positivity
  calc
    |degreeHazard D₂ D₃ D₄ d N x ^ 2 - degreeHazardSlope D₂ D₃ D₄ d N x| *
        dHat D₂ D₃ D₄ d N x ≤
      (12000 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2)) * d :=
        mul_le_mul hcoef hdHat hdHat0 hR0
    _ = 12000 * Gamma ^ 2 * d / (N ^ 2 * pV N x ^ 2) := by ring

/-- Pointwise curvature estimate for the degree error envelope. -/
theorem deltaCurvature_bound {D₂ D₃ D₄ Gamma epsilon d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N x) (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3)
    (hdelta : delta D₂ D₃ D₄ Gamma epsilon d N x ≤ d ^ (1 - epsilon / 64)) :
    |deltaCurvature D₂ D₃ D₄ Gamma epsilon d N x| ≤
      6000000000 * Gamma ^ 2 * d ^ (1 - epsilon / 64) /
        (N ^ 2 * pV N x ^ 2) := by
  have hGamma0 : 0 ≤ Gamma := by linarith
  have hGsq : Gamma ≤ Gamma ^ 2 := by nlinarith
  have hden : 0 < N * pV N x := mul_pos hN hpV
  have hden2 : 0 < (N * pV N x) ^ 2 := sq_pos_of_pos hden
  have hdenEq : N ^ 2 * pV N x ^ 2 = (N * pV N x) ^ 2 := by ring
  have hA0 := degreeHazard_nonneg hd hN hpV hD₂0 hD₃0 hD₄0 hpM0
  have hA := degreeHazard_le hd hN hGamma hpV hpV1 hpM0 hpM1 hD₂ hD₃ hD₄
  have hS0 : 0 ≤ degreeHazardSlope D₂ D₃ D₄ d N x := by
    unfold degreeHazardSlope
    positivity
  have hS := degreeHazardSlope_le (D₂ := D₂) hd hN hGamma hpV hpV1 hpM0 hpM1 hD₃ hD₄
  have hgamma0 : 0 ≤ gamma Gamma N x := by unfold gamma; positivity
  have hgammaSlope0 : 0 ≤ gammaSlope Gamma N x := by unfold gammaSlope; positivity
  have hrate :
      |gamma Gamma N x - degreeHazard D₂ D₃ D₄ d N x| ≤
        77000 * Gamma / (N * pV N x) := by
    calc
      _ ≤ |gamma Gamma N x| + |degreeHazard D₂ D₃ D₄ d N x| := abs_sub _ _
      _ = gamma Gamma N x + degreeHazard D₂ D₃ D₄ d N x := by
        rw [abs_of_nonneg hgamma0, abs_of_nonneg hA0]
      _ ≤ 76800 * Gamma / (N * pV N x) +
          104 * Gamma / (N * pV N x) := by
        unfold gamma
        exact add_le_add (le_refl _) hA
      _ = 76904 * Gamma / (N * pV N x) := by ring
      _ ≤ 77000 * Gamma / (N * pV N x) := by
        exact div_le_div_of_nonneg_right (by nlinarith) hden.le
  have hslopeDiff :
      |gammaSlope Gamma N x - degreeHazardSlope D₂ D₃ D₄ d N x| ≤
        616000 * Gamma ^ 2 / (N * pV N x) ^ 2 := by
    calc
      _ ≤ |gammaSlope Gamma N x| + |degreeHazardSlope D₂ D₃ D₄ d N x| :=
        abs_sub _ _
      _ = gammaSlope Gamma N x + degreeHazardSlope D₂ D₃ D₄ d N x := by
        rw [abs_of_nonneg hgammaSlope0, abs_of_nonneg hS0]
      _ ≤ 614400 * Gamma / (N * pV N x) ^ 2 +
          960 * Gamma / (N * pV N x) ^ 2 := by
        rw [hdenEq] at hS
        unfold gammaSlope
        rw [hdenEq]
        exact add_le_add (le_refl _) hS
      _ = 615360 * Gamma / (N * pV N x) ^ 2 := by ring
      _ ≤ 615360 * Gamma ^ 2 / (N * pV N x) ^ 2 :=
        div_le_div_of_nonneg_right (by nlinarith) hden2.le
      _ ≤ 616000 * Gamma ^ 2 / (N * pV N x) ^ 2 :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg Gamma]) hden2.le
  have hrateSq :
      (gamma Gamma N x - degreeHazard D₂ D₃ D₄ d N x) ^ 2 ≤
        (77000 * Gamma / (N * pV N x)) ^ 2 := by
    have hr0 : 0 ≤ 77000 * Gamma / (N * pV N x) := by positivity
    nlinarith [mul_self_le_mul_self (abs_nonneg _) hrate,
      sq_abs (gamma Gamma N x - degreeHazard D₂ D₃ D₄ d N x)]
  have hcoef :
      |(gamma Gamma N x - degreeHazard D₂ D₃ D₄ d N x) ^ 2 +
          gammaSlope Gamma N x - degreeHazardSlope D₂ D₃ D₄ d N x| ≤
        6000000000 * Gamma ^ 2 / (N * pV N x) ^ 2 := by
    calc
      _ ≤ |(gamma Gamma N x - degreeHazard D₂ D₃ D₄ d N x) ^ 2| +
          |gammaSlope Gamma N x - degreeHazardSlope D₂ D₃ D₄ d N x| := by
        simpa only [sub_eq_add_neg, add_assoc] using
          abs_add_le ((gamma Gamma N x - degreeHazard D₂ D₃ D₄ d N x) ^ 2)
            (gammaSlope Gamma N x - degreeHazardSlope D₂ D₃ D₄ d N x)
      _ = (gamma Gamma N x - degreeHazard D₂ D₃ D₄ d N x) ^ 2 +
          |gammaSlope Gamma N x - degreeHazardSlope D₂ D₃ D₄ d N x| := by
        rw [abs_of_nonneg (sq_nonneg _)]
      _ ≤ (77000 * Gamma / (N * pV N x)) ^ 2 +
          616000 * Gamma ^ 2 / (N * pV N x) ^ 2 := add_le_add hrateSq hslopeDiff
      _ = 5929616000 * Gamma ^ 2 / (N * pV N x) ^ 2 := by ring
      _ ≤ 6000000000 * Gamma ^ 2 / (N * pV N x) ^ 2 :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg Gamma]) hden2.le
  have hdelta0 : 0 ≤ delta D₂ D₃ D₄ Gamma epsilon d N x := (delta_pos hd hpV).le
  unfold deltaCurvature
  rw [abs_mul, abs_of_nonneg hdelta0]
  calc
    _ ≤ (6000000000 * Gamma ^ 2 / (N * pV N x) ^ 2) *
        d ^ (1 - epsilon / 64) :=
      mul_le_mul hcoef hdelta hdelta0 (by positivity)
    _ = 6000000000 * Gamma ^ 2 * d ^ (1 - epsilon / 64) /
        (N ^ 2 * pV N x ^ 2) := by rw [hdenEq]; ring

/-- A reusable one-step Taylor estimate.  It is stated in the exact form
needed by the discrete process: a derivative approximation whose error is
controlled uniformly on the next unit interval. -/
theorem oneStepTaylorEstimate {f f' : ℝ → ℝ} {x B : ℝ}
    (hB : 0 ≤ B)
    (hf : ∀ y ∈ Icc x (x + 1), HasDerivAt f (f' y) y)
    (hvar : ∀ y ∈ Icc x (x + 1), |f' y - f' x| ≤ B) :
    |f (x + 1) - f x - f' x| ≤ B := by
  let g : ℝ → ℝ := fun y => f y - f x - (y - x) * f' x
  have hg : ∀ y ∈ Icc x (x + 1), HasDerivAt g (f' y - f' x) y := by
    intro y hy
    have h := ((hf y hy).sub_const (f x)).sub
      (((hasDerivAt_id y).sub_const x).mul_const (f' x))
    change HasDerivAt (fun z => f z - f x - (z - x) * f' x) (f' y - f' x) y
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)).congr_deriv ?_
    · simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
    · ring
  have hbound : ∀ y ∈ Ico x (x + 1), ‖f' y - f' x‖ ≤ B := by
    intro y hy
    simpa [Real.norm_eq_abs] using hvar y ⟨hy.1, hy.2.le⟩
  have hle := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y hy => (hg y hy).hasDerivWithinAt) hbound (x + 1)
      (by constructor <;> linarith)
  simpa [g, Real.norm_eq_abs, mul_comm] using hle

/-- A derivative whose derivative is bounded by `B` on a unit interval
varies by at most `B` there. -/
theorem derivativeVariationOnUnit {f' f'' : ℝ → ℝ} {x B : ℝ}
    (hB : 0 ≤ B)
    (hf'' : ∀ y ∈ Icc x (x + 1), HasDerivAt f' (f'' y) y)
    (hsecond : ∀ y ∈ Icc x (x + 1), |f'' y| ≤ B) :
    ∀ y ∈ Icc x (x + 1), |f' y - f' x| ≤ B := by
  intro y hy
  have hderiv : ∀ z ∈ Icc x y, HasDerivWithinAt f' (f'' z) (Icc x y) z := by
    intro z hz
    exact (hf'' z ⟨hz.1, hz.2.trans hy.2⟩).hasDerivWithinAt
  have hbound : ∀ z ∈ Ico x y, ‖f'' z‖ ≤ B := by
    intro z hz
    simpa [Real.norm_eq_abs] using hsecond z ⟨hz.1, hz.2.le.trans hy.2⟩
  have hle := norm_image_sub_le_of_norm_deriv_le_segment'
    hderiv hbound y ⟨hy.1, le_rfl⟩
  have hylen : y - x ≤ 1 := by linarith [hy.2]
  calc
    |f' y - f' x| = ‖f' y - f' x‖ := by rw [Real.norm_eq_abs]
    _ ≤ B * (y - x) := hle
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left hylen hB
    _ = B := by ring

/-- Explicit numerical condition under which the degree curvature is small
enough for the source one-step error.  This is the large-`d` registry entry,
not a derivative-variation hypothesis. -/
def degreeLargeDCondition (Gamma epsilon d N P : ℝ) : Prop :=
  12000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2) ≤ d ^ (1 - epsilon) / N

/-- Concrete source hypotheses, uniform on one process step. -/
structure DegreeStepRegistry
    (D₂ D₃ D₄ Gamma epsilon d N x P : ℝ) : Prop where
  d_one : 1 ≤ d
  N_pos : 0 < N
  Gamma_one : 1 ≤ Gamma
  D₂_nonneg : 0 ≤ D₂
  D₃_nonneg : 0 ≤ D₃
  D₄_nonneg : 0 ≤ D₄
  D₂_bound : D₂ ≤ Gamma * d
  D₃_bound : D₃ ≤ Gamma * d ^ 2
  D₄_bound : D₄ ≤ Gamma * d ^ 3
  P_pos : 0 < P
  time_nonneg : ∀ y ∈ Icc x (x + 1), 0 ≤ y
  before_end : ∀ y ∈ Icc x (x + 1), 8 * y < N
  pV_floor : ∀ y ∈ Icc x (x + 1), P ≤ pV N y
  large_d : degreeLargeDCondition Gamma epsilon d N P

/-- Explicit large-`d` inequality for the degree error envelope. -/
def deltaLargeDCondition (Gamma epsilon d N P : ℝ) : Prop :=
  6000000000 * Gamma ^ 2 * d ^ (1 - epsilon / 64) / (N ^ 2 * P ^ 2) ≤
    d ^ (1 - epsilon) / N

/-- Source-scale component bounds needed for the exact degree-envelope
range, together with its explicit large-`d` inequality. -/
structure DeltaStepRegistry
    (D₂ D₃ D₄ Gamma epsilon d N x P : ℝ) : Prop where
  degree : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P
  xi_lower : ∀ y ∈ Icc x (x + 1),
    d ^ (-epsilon / 32) ≤ xi Gamma epsilon d N y
  dHat_lower : ∀ y ∈ Icc x (x + 1),
    d ^ (1 - epsilon / 32) ≤ dHat D₂ D₃ D₄ d N y
  xi_upper : ∀ y ∈ Icc x (x + 1),
    xi Gamma epsilon d N y ≤ d ^ (-epsilon / 64)
  large_delta : deltaLargeDCondition Gamma epsilon d N P

/-- The parenthesized trajectory scale in the definition of `zeta`. -/
def testInside (D₂ D₃ D₄ Gamma d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  zHat D₂ D₃ D₄ d N j s x +
    (Nat.choose j s : ℝ) * dHat D₂ D₃ D₄ d N x ^ s / (4 * Gamma * d ^ j)

/-- Uniform registry for one finite test.  Its curvature fields bound the
actual second derivatives `zHatCurvature` and `zetaCurvature`; they are not
first-derivative variation assumptions. -/
structure TestStepRegistry
    (D₂ D₃ D₄ Gamma epsilon d N x P : ℝ) (j s : ℕ) : Prop where
  delta : DeltaStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P
  s_le_j : s ≤ j
  j_le_four : j ≤ 4
  inside_lower : ∀ y ∈ Icc x (x + 1),
    d ^ ((s : ℝ) - j - epsilon / 32) ≤ testInside D₂ D₃ D₄ Gamma d N j s y
  inside_upper : ∀ y ∈ Icc x (x + 1),
    testInside D₂ D₃ D₄ Gamma d N j s y ≤
      d ^ ((s : ℝ) - j + 9 * epsilon / 1600)
  zHat_curvature : ∀ y ∈ Icc x (x + 1),
    |zHatCurvature D₂ D₃ D₄ d N j s y| ≤ d ^ ((s : ℝ) - j - epsilon) / N
  zeta_curvature : ∀ y ∈ Icc x (x + 1),
    |zetaCurvature D₂ D₃ D₄ Gamma epsilon d N j s y| ≤
      d ^ ((s : ℝ) - j - epsilon) / N

/-- A fully explicit source budget for the second derivative of `zeta`.
It is a function only of the fixed numeric parameters. -/
def zetaSourceCurvatureBudget (Gamma epsilon d N P : ℝ) (j s : ℕ) : ℝ :=
  let X := d ^ (-epsilon / 64)
  let S := d ^ ((s : ℝ) - j)
  let U := d ^ ((s : ℝ) - j + 9 * epsilon / 1600)
  let G := 76800 * Gamma / (N * P)
  let H := 614400 * Gamma / (N ^ 2 * P ^ 2)
  let V := 5000 * Gamma * S / (N * P)
  let B := d ^ ((s : ℝ) - j - epsilon) / N
  let W := B + 1000000 * Gamma ^ 2 * S / (N ^ 2 * P ^ 2)
  (G ^ 2 + H) * X * U + 2 * G * X * V + X * W

/-- Purely numerical large-parameter entries for a finite `(j,s)` test.
No trajectory or derivative occurs in these fields: the curvature fields
of `TestStepRegistry` are derived from the analytic formulas below. -/
structure TestLargeDCondition
    (Gamma epsilon d N P : ℝ) (j s : ℕ) : Prop where
  correction_denominator : 4 * Gamma ≤ d ^ (epsilon / 64)
  inside_upper : 12 * d ^ ((s : ℝ) - j) ≤
    d ^ ((s : ℝ) - j + 9 * epsilon / 1600)
  zHat_second_order :
    2000000 * (Gamma / (N * P)) ^ 2 * (d⁻¹) ^ (j - s) ≤
      d ^ ((s : ℝ) - j - epsilon) / N
  zeta_second_order :
    zetaSourceCurvatureBudget Gamma epsilon d N P j s ≤
      d ^ ((s : ℝ) - j - epsilon) / N

/-- Constructor exposing that the degree registry contains only the stated
source bounds and one explicit large-`d` inequality. -/
theorem DegreeStepRegistry.of_source
    {D₂ D₃ D₄ Gamma epsilon d N x P : ℝ}
    (hd : 1 ≤ d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) (hP : 0 < P)
    (htime : ∀ y ∈ Icc x (x + 1), 0 ≤ y)
    (hend : ∀ y ∈ Icc x (x + 1), 8 * y < N)
    (hfloor : ∀ y ∈ Icc x (x + 1), P ≤ pV N y)
    (hlarge : degreeLargeDCondition Gamma epsilon d N P) :
    DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P :=
  ⟨hd, hN, hGamma, hD₂0, hD₃0, hD₄0, hD₂, hD₃, hD₄, hP,
    htime, hend, hfloor, hlarge⟩

/-- `xi` bounds obtained directly from the stopping lower bound on `pV`
and the numerical amplification inequality. -/
theorem xi_source_bounds {Gamma epsilon d N y : ℝ}
    (hd : 1 ≤ d) (hGamma : 1 ≤ Gamma) (hepsilon : 0 ≤ epsilon)
    (hpV : 0 < pV N y) (hpV1 : pV N y ≤ 1)
    (hpVfloor : d ^ (-epsilon ^ 3) ≤ pV N y)
    (hamp : 9600 * Gamma * epsilon ^ 3 ≤ epsilon / 64) :
    d ^ (-epsilon / 32) ≤ xi Gamma epsilon d N y ∧
      xi Gamma epsilon d N y ≤ d ^ (-epsilon / 64) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hfacLower : 1 ≤ pV N y ^ (-9600 * Gamma) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpV hpV1 (by nlinarith)
  have hbasepos : 0 < d ^ (-epsilon ^ 3) := Real.rpow_pos_of_pos hdpos _
  have hfacUpper : pV N y ^ (-9600 * Gamma) ≤
      (d ^ (-epsilon ^ 3)) ^ (-9600 * Gamma) :=
    Real.rpow_le_rpow_of_nonpos hbasepos hpVfloor (by nlinarith)
  constructor
  · unfold xi
    calc
      d ^ (-epsilon / 32) = 1 * d ^ (-epsilon / 32) := by ring
      _ ≤ pV N y ^ (-9600 * Gamma) * d ^ (-epsilon / 32) :=
        mul_le_mul_of_nonneg_right hfacLower (Real.rpow_nonneg hdpos.le _)
  · unfold xi
    calc
      pV N y ^ (-9600 * Gamma) * d ^ (-epsilon / 32) ≤
          (d ^ (-epsilon ^ 3)) ^ (-9600 * Gamma) * d ^ (-epsilon / 32) :=
        mul_le_mul_of_nonneg_right hfacUpper (Real.rpow_nonneg hdpos.le _)
      _ = d ^ (9600 * Gamma * epsilon ^ 3 - epsilon / 32) := by
        rw [← Real.rpow_mul hdpos.le, ← Real.rpow_add hdpos]
        congr 1
        ring
      _ ≤ d ^ (-epsilon / 64) :=
        Real.rpow_le_rpow_of_exponent_le hd (by nlinarith)

/-- Lower bound for `dHat` from the source codegree bounds, the stopping
lower bound on `pV`, and two explicit large-`d` absorptions. -/
theorem dHat_source_lower {D₂ D₃ D₄ Gamma epsilon d N y : ℝ}
    (hd : 1 ≤ d) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N y) (hpVfloor : d ^ (-epsilon ^ 3) ≤ pV N y)
    (hpM0 : 0 ≤ pM d N y) (hpM1 : pM d N y ≤ d⁻¹)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3)
    (hvertex : 7 * epsilon ^ 3 ≤ epsilon / 64)
    (hexp : d ^ (-epsilon / 64) ≤ exp (-3 * Gamma)) :
    d ^ (1 - epsilon / 32) ≤ dHat D₂ D₃ D₄ d N y := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hGH := GammaHat_le_three_mul hdpos (by linarith) hpM0 hpM1
    hD₂0 hD₃0 hD₄0 hD₂ hD₃ hD₄
  have hexp' : exp (-3 * Gamma) ≤ exp (-GammaHat D₂ D₃ D₄ d N y) := by
    rw [Real.exp_le_exp]
    linarith
  have hbase0 : 0 ≤ d ^ (-epsilon ^ 3) := Real.rpow_nonneg hdpos.le _
  have hpVpow : (d ^ (-epsilon ^ 3)) ^ 7 ≤ pV N y ^ 7 :=
    pow_le_pow_left₀ hbase0 hpVfloor 7
  have hpower : d ^ (1 - epsilon / 32) ≤
      d ^ (1 - 7 * epsilon ^ 3 - epsilon / 64) :=
    Real.rpow_le_rpow_of_exponent_le hd (by nlinarith)
  have hid : d ^ (1 - 7 * epsilon ^ 3 - epsilon / 64) =
      d * (d ^ (-epsilon ^ 3)) ^ 7 * d ^ (-epsilon / 64) := by
    calc
      _ = d ^ (1 : ℝ) * d ^ ((-epsilon ^ 3) * (7 : ℝ)) *
          d ^ (-epsilon / 64) := by
        rw [← Real.rpow_add hdpos, ← Real.rpow_add hdpos]
        congr 1
        ring
      _ = d * (d ^ (-epsilon ^ 3)) ^ 7 * d ^ (-epsilon / 64) := by
        rw [Real.rpow_one, Real.rpow_mul hdpos.le]
        exact congrArg (fun z : ℝ => d * z * d ^ (-epsilon / 64))
          (Real.rpow_natCast (d ^ (-epsilon ^ 3)) 7)
  unfold dHat
  calc
    d ^ (1 - epsilon / 32) ≤ d ^ (1 - 7 * epsilon ^ 3 - epsilon / 64) := hpower
    _ = d * (d ^ (-epsilon ^ 3)) ^ 7 * d ^ (-epsilon / 64) := hid
    _ ≤ d * pV N y ^ 7 * d ^ (-epsilon / 64) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpVpow hdpos.le)
        (Real.rpow_nonneg hdpos.le _)
    _ ≤ d * pV N y ^ 7 * exp (-3 * Gamma) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hdpos.le (pow_nonneg hpV.le _))
    _ ≤ d * pV N y ^ 7 * exp (-GammaHat D₂ D₃ D₄ d N y) :=
      mul_le_mul_of_nonneg_left hexp'
        (mul_nonneg hdpos.le (pow_nonneg hpV.le _))

/-- A stronger version of `dHat_source_lower`, used for the finite-test
correction term.  The two losses of `epsilon / 512` combine to the
`epsilon / 256` loss in the conclusion. -/
theorem dHat_source_lower_strong {D₂ D₃ D₄ Gamma epsilon d N y : ℝ}
    (hd : 1 ≤ d) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N y) (hpVfloor : d ^ (-epsilon ^ 3) ≤ pV N y)
    (hpM0 : 0 ≤ pM d N y) (hpM1 : pM d N y ≤ d⁻¹)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3)
    (hvertex : 7 * epsilon ^ 3 ≤ epsilon / 512)
    (hexp : d ^ (-epsilon / 512) ≤ exp (-3 * Gamma)) :
    d ^ (1 - epsilon / 256) ≤ dHat D₂ D₃ D₄ d N y := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hGH := GammaHat_le_three_mul hdpos (by linarith) hpM0 hpM1
    hD₂0 hD₃0 hD₄0 hD₂ hD₃ hD₄
  have hexp' : exp (-3 * Gamma) ≤ exp (-GammaHat D₂ D₃ D₄ d N y) := by
    rw [Real.exp_le_exp]
    linarith
  have hbase0 : 0 ≤ d ^ (-epsilon ^ 3) := Real.rpow_nonneg hdpos.le _
  have hpVpow : (d ^ (-epsilon ^ 3)) ^ 7 ≤ pV N y ^ 7 :=
    pow_le_pow_left₀ hbase0 hpVfloor 7
  have hpower : d ^ (1 - epsilon / 256) ≤
      d ^ (1 - 7 * epsilon ^ 3 - epsilon / 512) :=
    Real.rpow_le_rpow_of_exponent_le hd (by nlinarith)
  have hid : d ^ (1 - 7 * epsilon ^ 3 - epsilon / 512) =
      d * (d ^ (-epsilon ^ 3)) ^ 7 * d ^ (-epsilon / 512) := by
    calc
      _ = d ^ (1 : ℝ) * d ^ ((-epsilon ^ 3) * (7 : ℝ)) *
          d ^ (-epsilon / 512) := by
        rw [← Real.rpow_add hdpos, ← Real.rpow_add hdpos]
        congr 1
        ring
      _ = d * (d ^ (-epsilon ^ 3)) ^ 7 * d ^ (-epsilon / 512) := by
        rw [Real.rpow_one, Real.rpow_mul hdpos.le]
        exact congrArg (fun z : ℝ => d * z * d ^ (-epsilon / 512))
          (Real.rpow_natCast (d ^ (-epsilon ^ 3)) 7)
  unfold dHat
  calc
    d ^ (1 - epsilon / 256) ≤
        d ^ (1 - 7 * epsilon ^ 3 - epsilon / 512) := hpower
    _ = d * (d ^ (-epsilon ^ 3)) ^ 7 * d ^ (-epsilon / 512) := hid
    _ ≤ d * pV N y ^ 7 * d ^ (-epsilon / 512) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpVpow hdpos.le)
        (Real.rpow_nonneg hdpos.le _)
    _ ≤ d * pV N y ^ 7 * exp (-3 * Gamma) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hdpos.le (pow_nonneg hpV.le _))
    _ ≤ d * pV N y ^ 7 * exp (-GammaHat D₂ D₃ D₄ d N y) :=
      mul_le_mul_of_nonneg_left hexp'
        (mul_nonneg hdpos.le (pow_nonneg hpV.le _))

/-- Source-scale upper bound for the bare test trajectory. -/
theorem zHat_source_upper {D₂ D₃ D₄ d N y : ℝ} {j s : ℕ}
    (hd : 1 ≤ d) (hpV : 0 < pV N y) (hpV1 : pV N y ≤ 1)
    (hpM0 : 0 ≤ pM d N y) (hpM1 : pM d N y ≤ d⁻¹)
    (hGH : 0 ≤ GammaHat D₂ D₃ D₄ d N y)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    zHat D₂ D₃ D₄ d N j s y ≤ 6 * d ^ ((s : ℝ) - j) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hq0 : 0 ≤ q D₂ D₃ D₄ d N y := (q_pos hpV).le
  have hq1 : q D₂ D₃ D₄ d N y ≤ 1 := q_le_one hpV.le hpV1 hGH
  have hqpow : q D₂ D₃ D₄ d N y ^ s ≤ 1 := pow_le_one₀ hq0 hq1
  have hmpow : pM d N y ^ (j - s) ≤ d ^ ((s : ℝ) - j) := by
    calc
      pM d N y ^ (j - s) ≤ (d⁻¹) ^ (j - s) :=
        pow_le_pow_left₀ hpM0 hpM1 _
      _ = d ^ ((s : ℝ) - j) := inv_pow_eq_rpow_sub hdpos hsj
  have hchoose : (j.choose s : ℝ) ≤ 6 := by
    exact_mod_cast choose_le_six hsj hj
  have hscale0 : 0 ≤ d ^ ((s : ℝ) - j) := Real.rpow_nonneg hdpos.le _
  unfold zHat
  calc
    (j.choose s : ℝ) * q D₂ D₃ D₄ d N y ^ s * pM d N y ^ (j - s) ≤
        6 * 1 * d ^ ((s : ℝ) - j) :=
      mul_le_mul (mul_le_mul hchoose hqpow (pow_nonneg hq0 _)
        (by norm_num)) hmpow (pow_nonneg hpM0 _) (by positivity)
    _ = 6 * d ^ ((s : ℝ) - j) := by ring

/-- Source-scale upper bound for the auxiliary correction in `testInside`. -/
theorem testCorrection_source_upper
    {D₂ D₃ D₄ Gamma d N y : ℝ} {j s : ℕ}
    (hd : 1 ≤ d) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N y) (hpV1 : pV N y ≤ 1)
    (hpM0 : 0 ≤ pM d N y)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    (j.choose s : ℝ) * dHat D₂ D₃ D₄ d N y ^ s /
        (4 * Gamma * d ^ j) ≤ 6 * d ^ ((s : ℝ) - j) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hGamma0 : 0 < Gamma := lt_of_lt_of_le (by norm_num) hGamma
  have hGH := GammaHat_nonneg hD₂0 hD₃0 hD₄0 hpM0
  have hdHat0 : 0 ≤ dHat D₂ D₃ D₄ d N y := (dHat_pos hdpos hpV).le
  have hdHat : dHat D₂ D₃ D₄ d N y ≤ d :=
    dHat_le_d hdpos.le hpV.le hpV1 hGH
  have hpows : dHat D₂ D₃ D₄ d N y ^ s ≤ d ^ s :=
    pow_le_pow_left₀ hdHat0 hdHat _
  have hchoose : (j.choose s : ℝ) ≤ 6 := by
    exact_mod_cast choose_le_six hsj hj
  have hnum : (j.choose s : ℝ) * dHat D₂ D₃ D₄ d N y ^ s ≤
      6 * d ^ s :=
    mul_le_mul hchoose hpows (pow_nonneg hdHat0 _) (by positivity)
  have hden0 : 0 < d ^ j := pow_pos hdpos _
  have hden : d ^ j ≤ 4 * Gamma * d ^ j := by
    nlinarith [mul_nonneg (show 0 ≤ 4 * Gamma - 1 by nlinarith) hden0.le]
  have hdiv := div_le_div₀ (by positivity) hnum hden0 hden
  calc
    (j.choose s : ℝ) * dHat D₂ D₃ D₄ d N y ^ s /
        (4 * Gamma * d ^ j) ≤ 6 * d ^ s / d ^ j := by
      simpa only using hdiv
    _ = 6 * d ^ ((s : ℝ) - j) := by
      rw [show 6 * d ^ s / d ^ j = 6 * (d ^ s / d ^ j) by ring,
        ← Real.rpow_natCast d s, ← Real.rpow_natCast d j,
        ← Real.rpow_sub hdpos]

/-- The parenthesized test scale is at most twelve times its natural
degree scale.  The public large-`d` condition uses the harmless constant
`32`, leaving slack for later products. -/
theorem testInside_source_upper
    {D₂ D₃ D₄ Gamma d N y : ℝ} {j s : ℕ}
    (hd : 1 ≤ d) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N y) (hpV1 : pV N y ≤ 1)
    (hpM0 : 0 ≤ pM d N y) (hpM1 : pM d N y ≤ d⁻¹)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    testInside D₂ D₃ D₄ Gamma d N j s y ≤
      12 * d ^ ((s : ℝ) - j) := by
  have hGH := GammaHat_nonneg hD₂0 hD₃0 hD₄0 hpM0
  unfold testInside
  linarith [zHat_source_upper hd hpV hpV1 hpM0 hpM1 hGH hsj hj,
    testCorrection_source_upper hd hGamma hpV hpV1 hpM0
      hD₂0 hD₃0 hD₄0 hsj hj]

/-- The auxiliary correction alone supplies the lower test scale.  All
losses are explicit powers of the source degree parameter. -/
theorem testCorrection_source_lower
    {D₂ D₃ D₄ Gamma epsilon d N y : ℝ} {j s : ℕ}
    (hd : 1 ≤ d) (hGamma : 1 ≤ Gamma) (hepsilon : 0 ≤ epsilon)
    (hpV : 0 < pV N y) (hsj : s ≤ j) (hj : j ≤ 4)
    (hdHatStrong : d ^ (1 - epsilon / 256) ≤ dHat D₂ D₃ D₄ d N y)
    (hdenom : 4 * Gamma ≤ d ^ (epsilon / 64)) :
    d ^ ((s : ℝ) - j - epsilon / 32) ≤
      (j.choose s : ℝ) * dHat D₂ D₃ D₄ d N y ^ s /
        (4 * Gamma * d ^ j) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hGamma0 : 0 < Gamma := lt_of_lt_of_le (by norm_num) hGamma
  have hs4 : (s : ℝ) ≤ 4 := by exact_mod_cast hsj.trans hj
  have hdHat0 : 0 ≤ dHat D₂ D₃ D₄ d N y := (dHat_pos hdpos hpV).le
  have hpows : d ^ ((s : ℝ) - (s : ℝ) * epsilon / 256) ≤
      dHat D₂ D₃ D₄ d N y ^ s := by
    calc
      d ^ ((s : ℝ) - (s : ℝ) * epsilon / 256) =
          (d ^ (1 - epsilon / 256)) ^ s := by
        rw [show (s : ℝ) - (s : ℝ) * epsilon / 256 =
            (1 - epsilon / 256) * (s : ℝ) by ring,
          Real.rpow_mul hdpos.le, Real.rpow_natCast]
      _ ≤ dHat D₂ D₃ D₄ d N y ^ s :=
        pow_le_pow_left₀ (Real.rpow_nonneg hdpos.le _) hdHatStrong _
  have hchooseNat : 1 ≤ j.choose s := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.choose_ne_zero hsj)
  have hchoose : (1 : ℝ) ≤ (j.choose s : ℝ) := by exact_mod_cast hchooseNat
  have hnum : d ^ ((s : ℝ) - (s : ℝ) * epsilon / 256) ≤
      (j.choose s : ℝ) * dHat D₂ D₃ D₄ d N y ^ s := by
    calc
      _ = 1 * d ^ ((s : ℝ) - (s : ℝ) * epsilon / 256) := by ring
      _ ≤ (j.choose s : ℝ) * dHat D₂ D₃ D₄ d N y ^ s :=
        mul_le_mul hchoose hpows (Real.rpow_nonneg hdpos.le _) (by norm_num)
  have hden : 4 * Gamma * d ^ j ≤ d ^ ((j : ℝ) + epsilon / 64) := by
    calc
      4 * Gamma * d ^ j ≤ d ^ (epsilon / 64) * d ^ j :=
        mul_le_mul_of_nonneg_right hdenom (pow_nonneg hdpos.le _)
      _ = d ^ ((j : ℝ) + epsilon / 64) := by
        rw [← Real.rpow_natCast d j, ← Real.rpow_add hdpos]
        congr 1
        ring
  have hactualDen : 0 < 4 * Gamma * d ^ j := by positivity
  have hupperDen : 0 < d ^ ((j : ℝ) + epsilon / 64) :=
    Real.rpow_pos_of_pos hdpos _
  have hexponent :
      (s : ℝ) - j - epsilon / 32 ≤
        ((s : ℝ) - (s : ℝ) * epsilon / 256) -
          ((j : ℝ) + epsilon / 64) := by
    nlinarith
  calc
    d ^ ((s : ℝ) - j - epsilon / 32) ≤
        d ^ (((s : ℝ) - (s : ℝ) * epsilon / 256) -
          ((j : ℝ) + epsilon / 64)) :=
      Real.rpow_le_rpow_of_exponent_le hd hexponent
    _ = d ^ ((s : ℝ) - (s : ℝ) * epsilon / 256) /
        d ^ ((j : ℝ) + epsilon / 64) := Real.rpow_sub hdpos _ _
    _ ≤ (j.choose s : ℝ) * dHat D₂ D₃ D₄ d N y ^ s /
        (4 * Gamma * d ^ j) :=
      div_le_div₀ (by positivity) hnum hactualDen hden

theorem testInside_source_lower
    {D₂ D₃ D₄ Gamma epsilon d N y : ℝ} {j s : ℕ}
    (hd : 1 ≤ d) (hGamma : 1 ≤ Gamma) (hepsilon : 0 ≤ epsilon)
    (hpV : 0 < pV N y) (hpM0 : 0 ≤ pM d N y)
    (hsj : s ≤ j) (hj : j ≤ 4)
    (hdHatStrong : d ^ (1 - epsilon / 256) ≤ dHat D₂ D₃ D₄ d N y)
    (hdenom : 4 * Gamma ≤ d ^ (epsilon / 64)) :
    d ^ ((s : ℝ) - j - epsilon / 32) ≤
      testInside D₂ D₃ D₄ Gamma d N j s y := by
  have hz0 : 0 ≤ zHat D₂ D₃ D₄ d N j s y := by
    unfold zHat
    exact mul_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (q_pos hpV).le _))
      (pow_nonneg hpM0 _)
  unfold testInside
  linarith [testCorrection_source_lower hd hGamma hepsilon hpV hsj hj
    hdHatStrong hdenom]

/-- Uniform constructor for the delta registry from the stopping inequality
and explicit large-`d` absorptions. -/
theorem DeltaStepRegistry.of_source
    {D₂ D₃ D₄ Gamma epsilon d N x P : ℝ}
    (R : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (hepsilon : 0 ≤ epsilon)
    (hstop : ∀ y ∈ Icc x (x + 1), d ^ (-epsilon ^ 3) ≤ pV N y)
    (hamp : 9600 * Gamma * epsilon ^ 3 ≤ epsilon / 64)
    (hvertex : 7 * epsilon ^ 3 ≤ epsilon / 64)
    (hexp : d ^ (-epsilon / 64) ≤ exp (-3 * Gamma))
    (hlarge : deltaLargeDCondition Gamma epsilon d N P) :
    DeltaStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P := by
  refine ⟨R, ?_, ?_, ?_, hlarge⟩
  · intro y hy
    exact (xi_source_bounds R.d_one R.Gamma_one hepsilon
      (pV_pos R.N_pos (R.before_end y hy))
      (pV_le_one R.N_pos (R.time_nonneg y hy)) (hstop y hy) hamp).1
  · intro y hy
    have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.d_one
    exact dHat_source_lower R.d_one R.Gamma_one
      (pV_pos R.N_pos (R.before_end y hy)) (hstop y hy)
      (pM_nonneg hd R.N_pos (R.time_nonneg y hy))
      (pM_le_inv hd R.N_pos (R.before_end y hy).le)
      R.D₂_nonneg R.D₃_nonneg R.D₄_nonneg R.D₂_bound R.D₃_bound R.D₄_bound
      hvertex hexp
  · intro y hy
    exact (xi_source_bounds R.d_one R.Gamma_one hepsilon
      (pV_pos R.N_pos (R.before_end y hy))
      (pV_le_one R.N_pos (R.time_nonneg y hy)) (hstop y hy) hamp).2

/-- Uniform curvature estimate obtained from `DegreeStepRegistry`. -/
theorem degreeCurvature_bound_of_registry
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ}
    (R : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (hy : y ∈ Icc x (x + 1)) :
    |degreeCurvature D₂ D₃ D₄ d N y| ≤ d ^ (1 - epsilon) / N := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.d_one
  have hpV := pV_pos R.N_pos (R.before_end y hy)
  have hpV1 := pV_le_one R.N_pos (R.time_nonneg y hy)
  have hpM0 := pM_nonneg hd R.N_pos (R.time_nonneg y hy)
  have hpM1 := pM_le_inv hd R.N_pos (R.before_end y hy).le
  have hpoint := degreeCurvature_bound hd R.N_pos R.Gamma_one hpV hpV1 hpM0 hpM1
    R.D₂_nonneg R.D₃_nonneg R.D₄_nonneg R.D₂_bound R.D₃_bound R.D₄_bound
  have hPpv : P ^ 2 ≤ pV N y ^ 2 := by
    nlinarith [mul_self_le_mul_self R.P_pos.le (R.pV_floor y hy)]
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos R.N_pos
  have hdenP : 0 < N ^ 2 * P ^ 2 := mul_pos hN2 (sq_pos_of_pos R.P_pos)
  have hdenV : 0 < N ^ 2 * pV N y ^ 2 := mul_pos hN2 (sq_pos_of_pos hpV)
  have hnum : 0 ≤ 12000 * Gamma ^ 2 * d := by positivity
  have hfloor :
      12000 * Gamma ^ 2 * d / (N ^ 2 * pV N y ^ 2) ≤
        12000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2) := by
    rw [div_le_div_iff₀ hdenV hdenP]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hPpv hN2.le) hnum
  exact hpoint.trans (hfloor.trans R.large_d)

/-- Actual one-step Taylor estimate for `dHat`.  In contrast with the
generic helper below, no derivative-variation hypothesis occurs: it is
derived from the source formulas and `DegreeStepRegistry`. -/
theorem dHat_oneStepTaylor_of_registry
    {D₂ D₃ D₄ Gamma epsilon d N x P : ℝ}
    (R : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P) :
    |dHat D₂ D₃ D₄ d N (x + 1) - dHat D₂ D₃ D₄ d N x -
        degreeRate D₂ D₃ D₄ d N x| ≤ d ^ (1 - epsilon) / N := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.d_one
  have hfirst : ∀ y ∈ Icc x (x + 1),
      HasDerivAt (dHat D₂ D₃ D₄ d N) (degreeRate D₂ D₃ D₄ d N y) y := by
    intro y hy
    exact hasDerivAt_dHat_degreeRate hd R.N_pos
      (pV_pos R.N_pos (R.before_end y hy))
  have hsecond : ∀ y ∈ Icc x (x + 1),
      HasDerivAt (degreeRate D₂ D₃ D₄ d N) (degreeCurvature D₂ D₃ D₄ d N y) y := by
    intro y hy
    exact hasDerivAt_degreeRate hd R.N_pos (pV_pos R.N_pos (R.before_end y hy))
  have hB : 0 ≤ d ^ (1 - epsilon) / N :=
    div_nonneg (Real.rpow_nonneg hd.le _) R.N_pos.le
  apply oneStepTaylorEstimate hB hfirst
  exact derivativeVariationOnUnit hB hsecond
    (fun y hy => degreeCurvature_bound_of_registry R hy)

theorem delta_bounds_of_registry
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ}
    (R : DeltaStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (hy : y ∈ Icc x (x + 1)) :
    d ^ (1 - epsilon / 16) ≤ delta D₂ D₃ D₄ Gamma epsilon d N y ∧
      delta D₂ D₃ D₄ Gamma epsilon d N y ≤ d ^ (1 - epsilon / 64) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.degree.d_one
  have hpV := pV_pos R.degree.N_pos (R.degree.before_end y hy)
  have hpM0 := pM_nonneg hd R.degree.N_pos (R.degree.time_nonneg y hy)
  have hGH := GammaHat_nonneg R.degree.D₂_nonneg R.degree.D₃_nonneg
    R.degree.D₄_nonneg hpM0
  have hdUpper := dHat_le_d hd.le hpV.le
    (pV_le_one R.degree.N_pos (R.degree.time_nonneg y hy)) hGH
  exact delta_bounds_exact hd hpV (R.xi_lower y hy) (R.dHat_lower y hy)
    (R.xi_upper y hy) hdUpper

theorem deltaCurvature_bound_of_registry
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ}
    (R : DeltaStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (hy : y ∈ Icc x (x + 1)) :
    |deltaCurvature D₂ D₃ D₄ Gamma epsilon d N y| ≤ d ^ (1 - epsilon) / N := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.degree.d_one
  have hpV := pV_pos R.degree.N_pos (R.degree.before_end y hy)
  have hpV1 := pV_le_one R.degree.N_pos (R.degree.time_nonneg y hy)
  have hpM0 := pM_nonneg hd R.degree.N_pos (R.degree.time_nonneg y hy)
  have hpM1 := pM_le_inv hd R.degree.N_pos (R.degree.before_end y hy).le
  have hpoint := deltaCurvature_bound hd R.degree.N_pos R.degree.Gamma_one hpV hpV1
    hpM0 hpM1 R.degree.D₂_nonneg R.degree.D₃_nonneg R.degree.D₄_nonneg
    R.degree.D₂_bound R.degree.D₃_bound R.degree.D₄_bound
    (delta_bounds_of_registry R hy).2
  have hPpv : P ^ 2 ≤ pV N y ^ 2 := by
    nlinarith [mul_self_le_mul_self R.degree.P_pos.le (R.degree.pV_floor y hy)]
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos R.degree.N_pos
  have hdenP : 0 < N ^ 2 * P ^ 2 := mul_pos hN2 (sq_pos_of_pos R.degree.P_pos)
  have hdenV : 0 < N ^ 2 * pV N y ^ 2 := mul_pos hN2 (sq_pos_of_pos hpV)
  have hnum : 0 ≤ 6000000000 * Gamma ^ 2 * d ^ (1 - epsilon / 64) := by positivity
  have hfloor :
      6000000000 * Gamma ^ 2 * d ^ (1 - epsilon / 64) /
          (N ^ 2 * pV N y ^ 2) ≤
        6000000000 * Gamma ^ 2 * d ^ (1 - epsilon / 64) /
          (N ^ 2 * P ^ 2) := by
    rw [div_le_div_iff₀ hdenV hdenP]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hPpv hN2.le) hnum
  exact hpoint.trans (hfloor.trans R.large_delta)

/-- Actual one-step Taylor estimate for `delta`, with variation derived
from `deltaCurvature`. -/
theorem delta_oneStepTaylor_of_registry
    {D₂ D₃ D₄ Gamma epsilon d N x P : ℝ}
    (R : DeltaStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P) :
    |delta D₂ D₃ D₄ Gamma epsilon d N (x + 1) -
        delta D₂ D₃ D₄ Gamma epsilon d N x -
        deltaRate D₂ D₃ D₄ Gamma epsilon d N x| ≤ d ^ (1 - epsilon) / N := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.degree.d_one
  have hfirst : ∀ y ∈ Icc x (x + 1),
      HasDerivAt (delta D₂ D₃ D₄ Gamma epsilon d N)
        (deltaRate D₂ D₃ D₄ Gamma epsilon d N y) y := by
    intro y hy
    exact hasDerivAt_delta_rate hd R.degree.N_pos
      (pV_pos R.degree.N_pos (R.degree.before_end y hy))
  have hsecond : ∀ y ∈ Icc x (x + 1),
      HasDerivAt (deltaRate D₂ D₃ D₄ Gamma epsilon d N)
        (deltaCurvature D₂ D₃ D₄ Gamma epsilon d N y) y := by
    intro y hy
    exact hasDerivAt_deltaRate hd R.degree.N_pos
      (pV_pos R.degree.N_pos (R.degree.before_end y hy))
  have hB : 0 ≤ d ^ (1 - epsilon) / N :=
    div_nonneg (Real.rpow_nonneg hd.le _) R.degree.N_pos.le
  apply oneStepTaylorEstimate hB hfirst
  exact derivativeVariationOnUnit hB hsecond
    (fun y hy => deltaCurvature_bound_of_registry R hy)

/-- Exact lower and upper source exponents for a test envelope. -/
theorem zeta_bounds_of_registry
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ} {j s : ℕ}
    (R : TestStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P j s)
    (hy : y ∈ Icc x (x + 1)) :
    d ^ ((s : ℝ) - j - epsilon / 16) ≤
        zeta D₂ D₃ D₄ Gamma epsilon d N j s y ∧
      zeta D₂ D₃ D₄ Gamma epsilon d N j s y ≤
        d ^ ((s : ℝ) - j - epsilon / 100) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.delta.degree.d_one
  have hpV := pV_pos R.delta.degree.N_pos (R.delta.degree.before_end y hy)
  have hxi0 : 0 ≤ xi Gamma epsilon d N y := (xi_pos hd hpV).le
  have hin0 : 0 ≤ testInside D₂ D₃ D₄ Gamma d N j s y :=
    (Real.rpow_nonneg hd.le _).trans (R.inside_lower y hy)
  constructor
  · change d ^ ((s : ℝ) - j - epsilon / 16) ≤
      xi Gamma epsilon d N y * testInside D₂ D₃ D₄ Gamma d N j s y
    calc
      d ^ ((s : ℝ) - j - epsilon / 16) =
          d ^ (-epsilon / 32) * d ^ ((s : ℝ) - j - epsilon / 32) := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
      _ ≤ xi Gamma epsilon d N y * testInside D₂ D₃ D₄ Gamma d N j s y :=
        mul_le_mul (R.delta.xi_lower y hy) (R.inside_lower y hy)
          (Real.rpow_nonneg hd.le _) hxi0
  · change xi Gamma epsilon d N y * testInside D₂ D₃ D₄ Gamma d N j s y ≤
      d ^ ((s : ℝ) - j - epsilon / 100)
    calc
      _ ≤ d ^ (-epsilon / 64) * d ^ ((s : ℝ) - j + 9 * epsilon / 1600) :=
        mul_le_mul (R.delta.xi_upper y hy) (R.inside_upper y hy) hin0
          (Real.rpow_nonneg hd.le _)
      _ = d ^ ((s : ℝ) - j - epsilon / 100) := by
        rw [← Real.rpow_add hd]
        congr 1
        ring

/-- No-`hvar` one-step estimate for an actual test trajectory. -/
theorem zHat_oneStepTaylor_of_registry
    {D₂ D₃ D₄ Gamma epsilon d N x P : ℝ} {j s : ℕ}
    (R : TestStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P j s) :
    |zHat D₂ D₃ D₄ d N j s (x + 1) - zHat D₂ D₃ D₄ d N j s x -
        zHatRate D₂ D₃ D₄ d N j s x| ≤ d ^ ((s : ℝ) - j - epsilon) / N := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.delta.degree.d_one
  have hfirst : ∀ y ∈ Icc x (x + 1),
      HasDerivAt (zHat D₂ D₃ D₄ d N j s) (zHatRate D₂ D₃ D₄ d N j s y) y := by
    intro y hy
    exact hasDerivAt_zHat_rate hd R.delta.degree.N_pos
      (pV_pos R.delta.degree.N_pos (R.delta.degree.before_end y hy))
      R.s_le_j R.j_le_four
  have hsecond : ∀ y ∈ Icc x (x + 1),
      HasDerivAt (zHatRate D₂ D₃ D₄ d N j s)
        (zHatCurvature D₂ D₃ D₄ d N j s y) y := by
    intro y hy
    exact hasDerivAt_zHatRate hd R.delta.degree.N_pos
      (pV_pos R.delta.degree.N_pos (R.delta.degree.before_end y hy))
  have hB : 0 ≤ d ^ ((s : ℝ) - j - epsilon) / N :=
    div_nonneg (Real.rpow_nonneg hd.le _) R.delta.degree.N_pos.le
  apply oneStepTaylorEstimate hB hfirst
  exact derivativeVariationOnUnit hB hsecond R.zHat_curvature

/-- No-`hvar` one-step estimate for an actual test error envelope. -/
theorem zeta_oneStepTaylor_of_registry
    {D₂ D₃ D₄ Gamma epsilon d N x P : ℝ} {j s : ℕ}
    (R : TestStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P j s) :
    |zeta D₂ D₃ D₄ Gamma epsilon d N j s (x + 1) -
        zeta D₂ D₃ D₄ Gamma epsilon d N j s x -
        zetaRate D₂ D₃ D₄ Gamma epsilon d N j s x| ≤
      d ^ ((s : ℝ) - j - epsilon) / N := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.delta.degree.d_one
  have hGamma : 0 < Gamma := lt_of_lt_of_le (by norm_num) R.delta.degree.Gamma_one
  have hfirst : ∀ y ∈ Icc x (x + 1),
      HasDerivAt (zeta D₂ D₃ D₄ Gamma epsilon d N j s)
        (zetaRate D₂ D₃ D₄ Gamma epsilon d N j s y) y := by
    intro y hy
    exact hasDerivAt_zeta_rate hd R.delta.degree.N_pos hGamma
      (pV_pos R.delta.degree.N_pos (R.delta.degree.before_end y hy))
      R.s_le_j R.j_le_four
  have hsecond : ∀ y ∈ Icc x (x + 1),
      HasDerivAt (zetaRate D₂ D₃ D₄ Gamma epsilon d N j s)
        (zetaCurvature D₂ D₃ D₄ Gamma epsilon d N j s y) y := by
    intro y hy
    exact hasDerivAt_zetaRate hd R.delta.degree.N_pos hGamma
      (pV_pos R.delta.degree.N_pos (R.delta.degree.before_end y hy))
  have hB : 0 ≤ d ^ ((s : ℝ) - j - epsilon) / N :=
    div_nonneg (Real.rpow_nonneg hd.le _) R.delta.degree.N_pos.le
  apply oneStepTaylorEstimate hB hfirst
  exact derivativeVariationOnUnit hB hsecond R.zeta_curvature

/-! ### Explicit second derivatives of finite-test trajectories -/

def qHazard (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  8 / (d * N) * conflictLoad D₂ D₃ D₄ d N x + 64 / (N * pV N x)

def qHazardSlope (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  (8 / (d * N)) ^ 2 * (2 * D₃ + 6 * D₄ * pM d N x) +
    512 / (N ^ 2 * pV N x ^ 2)

def qRate (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  -qHazard D₂ D₃ D₄ d N x * q D₂ D₃ D₄ d N x

def qCurvature (D₂ D₃ D₄ d N x : ℝ) : ℝ :=
  (qHazard D₂ D₃ D₄ d N x ^ 2 - qHazardSlope D₂ D₃ D₄ d N x) *
    q D₂ D₃ D₄ d N x

theorem hasDerivAt_q_qRate {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (q D₂ D₃ D₄ d N) (qRate D₂ D₃ D₄ d N x) x := by
  have h := hasDerivAt_q_eq (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV
  refine h.congr_deriv ?_
  rw [show
    -((cHat D₂ D₃ D₄ d N x + 8 * dHat D₂ D₃ D₄ d N x) *
        q D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x) =
      -(cHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x +
          8 * (dHat D₂ D₃ D₄ d N x / hHat D₂ D₃ D₄ d N x)) *
        q D₂ D₃ D₄ d N x by field_simp]
  rw [cHat_div_hHat hd hN hpV, dHat_div_hHat hd hN hpV]
  unfold qRate qHazard conflictLoad
  ring

theorem hasDerivAt_qHazard {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (qHazard D₂ D₃ D₄ d N)
      (qHazardSlope D₂ D₃ D₄ d N x) x := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hpV0 : pV N x ≠ 0 := ne_of_gt hpV
  have hconf := (hasDerivAt_conflictLoad D₂ D₃ D₄ d N x).const_mul (8 / (d * N))
  have hden := ((hasDerivAt_const x N).mul (hasDerivAt_pV N x)).inv
    (mul_ne_zero hN0 hpV0)
  have hgeom := hden.const_mul 64
  have h := hconf.add hgeom
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [qHazard, conflictLoad, Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    ring
  · unfold qHazardSlope
    simp only [Pi.mul_apply]
    field_simp
    ring

theorem hasDerivAt_qRate {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (qRate D₂ D₃ D₄ d N) (qCurvature D₂ D₃ D₄ d N x) x := by
  have h := (hasDerivAt_qHazard (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    hd hN hpV).neg.mul (hasDerivAt_q_qRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
      hd hN hpV)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [qRate, Pi.mul_apply, Pi.neg_apply]
  · unfold qCurvature qRate
    simp only [Pi.neg_apply]
    ring

theorem qHazard_nonneg {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hpM0 : 0 ≤ pM d N x) : 0 ≤ qHazard D₂ D₃ D₄ d N x := by
  unfold qHazard
  have := conflictLoad_nonneg hD₂0 hD₃0 hD₄0 hpM0
  positivity

theorem qHazard_le {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N x) (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    qHazard D₂ D₃ D₄ d N x ≤ 112 * Gamma / (N * pV N x) := by
  have hGamma0 : 0 ≤ Gamma := by linarith
  have hload := conflictLoad_le_six_mul hd hGamma0 hpM0 hpM1 hD₂ hD₃ hD₄
  have hden : 0 < N * pV N x := mul_pos hN hpV
  have hconf :
      8 / (d * N) * conflictLoad D₂ D₃ D₄ d N x ≤
        48 * Gamma / (N * pV N x) := by
    apply (le_div_iff₀ hden).2
    calc
      (8 / (d * N) * conflictLoad D₂ D₃ D₄ d N x) * (N * pV N x) ≤
          (8 / (d * N) * (6 * Gamma * d)) * (N * pV N x) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hload (by positivity)) hden.le
      _ = 48 * Gamma * pV N x := by field_simp; ring
      _ ≤ 48 * Gamma * 1 :=
        mul_le_mul_of_nonneg_left hpV1 (by positivity)
      _ = 48 * Gamma := by ring
  have hgeom : 64 / (N * pV N x) ≤ 64 * Gamma / (N * pV N x) :=
    div_le_div_of_nonneg_right (by nlinarith) hden.le
  unfold qHazard
  calc
    8 / (d * N) * conflictLoad D₂ D₃ D₄ d N x + 64 / (N * pV N x) ≤
        48 * Gamma / (N * pV N x) + 64 * Gamma / (N * pV N x) :=
      add_le_add hconf hgeom
    _ = 112 * Gamma / (N * pV N x) := by ring

theorem qHazardSlope_nonneg {D₂ D₃ D₄ d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x)
    (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄) (hpM0 : 0 ≤ pM d N x) :
    0 ≤ qHazardSlope D₂ D₃ D₄ d N x := by
  unfold qHazardSlope
  positivity

theorem qHazardSlope_le {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N x) (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₃ : D₃ ≤ Gamma * d ^ 2) (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    qHazardSlope D₂ D₃ D₄ d N x ≤
      1024 * Gamma / (N ^ 2 * pV N x ^ 2) := by
  have hGamma0 : 0 ≤ Gamma := by linarith
  have hslope := conflictSlope_le_eight_mul hd hGamma0 hpM0 hpM1 hD₃ hD₄
  have hden2 : 0 < N ^ 2 * pV N x ^ 2 := mul_pos (sq_pos_of_pos hN) (sq_pos_of_pos hpV)
  have hpVsq : pV N x ^ 2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self hpV.le hpV1]
  have hconf :
      (8 / (d * N)) ^ 2 * (2 * D₃ + 6 * D₄ * pM d N x) ≤
        512 * Gamma / (N ^ 2 * pV N x ^ 2) := by
    apply (le_div_iff₀ hden2).2
    calc
      ((8 / (d * N)) ^ 2 * (2 * D₃ + 6 * D₄ * pM d N x)) *
          (N ^ 2 * pV N x ^ 2) ≤
        ((8 / (d * N)) ^ 2 * (8 * Gamma * d ^ 2)) *
          (N ^ 2 * pV N x ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hslope (sq_nonneg _)) hden2.le
      _ = 512 * Gamma * pV N x ^ 2 := by field_simp; ring
      _ ≤ 512 * Gamma := by nlinarith
  have hgeom : 512 / (N ^ 2 * pV N x ^ 2) ≤
      512 * Gamma / (N ^ 2 * pV N x ^ 2) :=
    div_le_div_of_nonneg_right (by nlinarith) hden2.le
  unfold qHazardSlope
  calc
    (8 / (d * N)) ^ 2 * (2 * D₃ + 6 * D₄ * pM d N x) +
        512 / (N ^ 2 * pV N x ^ 2) ≤
      512 * Gamma / (N ^ 2 * pV N x ^ 2) +
        512 * Gamma / (N ^ 2 * pV N x ^ 2) := add_le_add hconf hgeom
    _ = 1024 * Gamma / (N ^ 2 * pV N x ^ 2) := by ring

theorem qRate_bound {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N x) (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    |qRate D₂ D₃ D₄ d N x| ≤ 112 * Gamma / (N * pV N x) := by
  have hA0 := qHazard_nonneg hd hN hpV hD₂0 hD₃0 hD₄0 hpM0
  have hA := qHazard_le hd hN hGamma hpV hpV1 hpM0 hpM1 hD₂ hD₃ hD₄
  have hGH := GammaHat_nonneg hD₂0 hD₃0 hD₄0 hpM0
  have hq0 : 0 ≤ q D₂ D₃ D₄ d N x := (q_pos hpV).le
  have hq1 := q_le_one hpV.le hpV1 hGH
  unfold qRate
  rw [abs_mul, abs_neg, abs_of_nonneg hA0, abs_of_nonneg hq0]
  calc
    qHazard D₂ D₃ D₄ d N x * q D₂ D₃ D₄ d N x ≤
        (112 * Gamma / (N * pV N x)) * 1 :=
      mul_le_mul hA hq1 hq0 (by positivity)
    _ = 112 * Gamma / (N * pV N x) := by ring

theorem qCurvature_bound {D₂ D₃ D₄ Gamma d N x : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N x) (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) :
    |qCurvature D₂ D₃ D₄ d N x| ≤
      14000 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) := by
  have hA0 := qHazard_nonneg hd hN hpV hD₂0 hD₃0 hD₄0 hpM0
  have hA := qHazard_le hd hN hGamma hpV hpV1 hpM0 hpM1 hD₂ hD₃ hD₄
  have hS0 := qHazardSlope_nonneg (D₂ := D₂) hd hN hpV hD₃0 hD₄0 hpM0
  have hS := qHazardSlope_le (D₂ := D₂) hd hN hGamma hpV hpV1 hpM0 hpM1 hD₃ hD₄
  have hGH := GammaHat_nonneg hD₂0 hD₃0 hD₄0 hpM0
  have hq0 : 0 ≤ q D₂ D₃ D₄ d N x := (q_pos hpV).le
  have hq1 := q_le_one hpV.le hpV1 hGH
  have hden : 0 < N * pV N x := mul_pos hN hpV
  have hden2 : N ^ 2 * pV N x ^ 2 = (N * pV N x) ^ 2 := by ring
  have hAsq : qHazard D₂ D₃ D₄ d N x ^ 2 ≤
      (112 * Gamma / (N * pV N x)) ^ 2 := by
    nlinarith [mul_self_le_mul_self hA0 hA]
  have hcoef : |qHazard D₂ D₃ D₄ d N x ^ 2 -
      qHazardSlope D₂ D₃ D₄ d N x| ≤
        14000 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) := by
    rw [abs_sub_le_iff]
    have hS' : qHazardSlope D₂ D₃ D₄ d N x ≤
        1024 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) := by
      calc
        _ ≤ 1024 * Gamma / (N ^ 2 * pV N x ^ 2) := hS
        _ ≤ 1024 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) :=
          div_le_div_of_nonneg_right (by nlinarith) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hAsq' : qHazard D₂ D₃ D₄ d N x ^ 2 ≤
        12544 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) := by
      calc
        _ ≤ (112 * Gamma / (N * pV N x)) ^ 2 := hAsq
        _ = 12544 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) := by ring
    have hAfinal : qHazard D₂ D₃ D₄ d N x ^ 2 ≤
        14000 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) :=
      hAsq'.trans (div_le_div_of_nonneg_right (by nlinarith [sq_nonneg Gamma])
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    have hSfinal : qHazardSlope D₂ D₃ D₄ d N x ≤
        14000 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) :=
      hS'.trans (div_le_div_of_nonneg_right (by nlinarith [sq_nonneg Gamma])
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    constructor
    · linarith
    · nlinarith [sq_nonneg (qHazard D₂ D₃ D₄ d N x)]
  unfold qCurvature
  rw [abs_mul, abs_of_nonneg hq0]
  calc
    _ ≤ (14000 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2)) * 1 :=
      mul_le_mul hcoef hq1 hq0 (by positivity)
    _ = 14000 * Gamma ^ 2 / (N ^ 2 * pV N x ^ 2) := by ring

def zHatRawRate (D₂ D₃ D₄ d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose j s : ℝ) *
    (s * q D₂ D₃ D₄ d N x ^ (s - 1) * qRate D₂ D₃ D₄ d N x *
        pM d N x ^ (j - s) +
      q D₂ D₃ D₄ d N x ^ s *
        ((j - s : ℕ) * pM d N x ^ (j - s - 1) * (8 / (d * N))))

theorem hasDerivAt_zHat_rawRate {D₂ D₃ D₄ d N x : ℝ} (j s : ℕ)
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x) :
    HasDerivAt (zHat D₂ D₃ D₄ d N j s) (zHatRawRate D₂ D₃ D₄ d N j s x) x := by
  have hq := hasDerivAt_q_qRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV
  have hm := hasDerivAt_pM d N x
  have h := ((hq.pow s).mul (hm.pow (j-s))).const_mul (Nat.choose j s : ℝ)
  unfold zHat zHatRawRate
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [Pi.mul_apply, Pi.pow_apply]

theorem zHatRate_eq_rawRate {D₂ D₃ D₄ d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    zHatRate D₂ D₃ D₄ d N j s x = zHatRawRate D₂ D₃ D₄ d N j s x :=
  (hasDerivAt_zHat_rate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV hsj hj).unique
    (hasDerivAt_zHat_rawRate j s hd hN hpV)

def zHatRawCurvature (D₂ D₃ D₄ d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose j s : ℝ) *
    (((s * (s - 1) : ℕ) : ℝ) * q D₂ D₃ D₄ d N x ^ (s - 2) *
          qRate D₂ D₃ D₄ d N x ^ 2 * pM d N x ^ (j - s) +
      (s : ℝ) * q D₂ D₃ D₄ d N x ^ (s - 1) *
          qCurvature D₂ D₃ D₄ d N x * pM d N x ^ (j - s) +
      2 * (s : ℝ) * ((j - s : ℕ) : ℝ) * q D₂ D₃ D₄ d N x ^ (s - 1) *
          qRate D₂ D₃ D₄ d N x * pM d N x ^ (j - s - 1) * (8 / (d * N)) +
      (((j - s) * (j - s - 1) : ℕ) : ℝ) * q D₂ D₃ D₄ d N x ^ s *
          pM d N x ^ (j - s - 2) * (8 / (d * N)) ^ 2)

theorem hasDerivAt_zHatRawRate {D₂ D₃ D₄ d N x : ℝ} (j s : ℕ)
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    HasDerivAt (zHatRawRate D₂ D₃ D₄ d N j s)
      (zHatRawCurvature D₂ D₃ D₄ d N j s x) x := by
  have hq := hasDerivAt_q_qRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV
  have hqr := hasDerivAt_qRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV
  have hm := hasDerivAt_pM d N x
  have hA := (((hq.pow (s - 1)).mul hqr).mul (hm.pow (j-s))).const_mul (s : ℝ)
  have hB := (((hq.pow s).mul (hm.pow (j-s-1))).const_mul ((j-s : ℕ) : ℝ))
    |>.mul_const (8/(d*N))
  have h := (hA.add hB).const_mul (Nat.choose j s : ℝ)
  unfold zHatRawRate zHatRawCurvature
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · interval_cases j <;> interval_cases s <;>
      norm_num [Nat.choose] <;> ring

theorem zHatCurvature_eq_raw {D₂ D₃ D₄ d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hpV : 0 < pV N x)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    zHatCurvature D₂ D₃ D₄ d N j s x = zHatRawCurvature D₂ D₃ D₄ d N j s x := by
  have hevent : ∀ᶠ y in nhds x, 0 < pV N y :=
    (hasDerivAt_pV N x).continuousAt.eventually (Ioi_mem_nhds hpV)
  have heq : zHatRate D₂ D₃ D₄ d N j s =ᶠ[nhds x]
      zHatRawRate D₂ D₃ D₄ d N j s := by
    filter_upwards [hevent] with y hy
    exact zHatRate_eq_rawRate hd hN hy hsj hj
  have hraw := hasDerivAt_zHatRawRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    j s hd hN hpV hsj hj
  have hr : HasDerivAt (zHatRate D₂ D₃ D₄ d N j s)
      (zHatRawCurvature D₂ D₃ D₄ d N j s x) x := hraw.congr_of_eventuallyEq heq
  exact (hasDerivAt_zHatRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV).unique hr

def rawCore (Q M QR QC V : ℝ) (j s : ℕ) : ℝ :=
  (((s * (s - 1) : ℕ) : ℝ) * Q ^ (s - 2) * QR ^ 2 * M ^ (j - s) +
    (s : ℝ) * Q ^ (s - 1) * QC * M ^ (j - s) +
    2 * (s : ℝ) * ((j - s : ℕ) : ℝ) * Q ^ (s - 1) * QR * M ^ (j - s - 1) * V +
    (((j - s) * (j - s - 1) : ℕ) : ℝ) * Q ^ s * M ^ (j - s - 2) * V ^ 2)

theorem rawCore_bound {Q M QR QC V U R : ℝ} {j s : ℕ}
    (hsj : s ≤ j) (hj : j ≤ 4)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hM0 : 0 ≤ M) (hM1 : M ≤ U)
    (hU0 : 0 ≤ U) (hR0 : 0 ≤ R)
    (hQR : |QR| ≤ 112 * R) (hQC : |QC| ≤ 14000 * R ^ 2)
    (hV : |V| ≤ 8 * R * U) :
    |(Nat.choose j s : ℝ) * rawCore Q M QR QC V j s| ≤
      2000000 * R ^ 2 * U ^ (j - s) := by
  have hs4 : s ≤ 4 := hsj.trans hj
  have hr4 : j - s ≤ 4 := (Nat.sub_le j s).trans hj
  have hchoose0 : 0 ≤ (Nat.choose j s : ℝ) := by positivity
  have hchoose6 : (Nat.choose j s : ℝ) ≤ 6 := by
    interval_cases j <;> interval_cases s <;> norm_num [Nat.choose]
  have hs12 : (((s * (s - 1) : ℕ) : ℝ)) ≤ 12 := by
    interval_cases s <;> norm_num
  have hs4r : (s : ℝ) ≤ 4 := by exact_mod_cast hs4
  have hcross32 : 2 * (s : ℝ) * ((j - s : ℕ) : ℝ) ≤ 32 := by
    have hr4' : ((j - s : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hr4
    nlinarith
  have hr12 : ((((j - s) * (j - s - 1) : ℕ) : ℝ)) ≤ 12 := by
    have := hr4
    interval_cases (j - s) <;> norm_num
  have hQpow (n : ℕ) : Q ^ n ≤ 1 := pow_le_one₀ hQ0 hQ1
  have hMpow (n : ℕ) : M ^ n ≤ U ^ n := pow_le_pow_left₀ hM0 hM1 n
  have hQR0 : 0 ≤ 112 * R := mul_nonneg (by norm_num) hR0
  have hQC0 : 0 ≤ 14000 * R ^ 2 := by positivity
  have hV0 : 0 ≤ 8 * R * U := by positivity
  have hQRsq : |QR| ^ 2 ≤ (112 * R) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hQR 2
  let r := j - s
  have hT1 :
      |(((s * (s - 1) : ℕ) : ℝ) * Q ^ (s - 2) * QR ^ 2 * M ^ r)| ≤
        150528 * R ^ 2 * U ^ r := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity),
      abs_of_nonneg (pow_nonneg hQ0 _), abs_pow, abs_of_nonneg (pow_nonneg hM0 _)]
    calc
      _ ≤ 12 * 1 * (112 * R) ^ 2 * U ^ r := by
        gcongr
        exact hQpow _
      _ = 150528 * R ^ 2 * U ^ r := by ring
  have hT2 :
      |(s : ℝ) * Q ^ (s - 1) * QC * M ^ r| ≤ 56000 * R ^ 2 * U ^ r := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity),
      abs_of_nonneg (pow_nonneg hQ0 _), abs_of_nonneg (pow_nonneg hM0 _)]
    calc
      _ ≤ 4 * 1 * (14000 * R ^ 2) * U ^ r := by
        gcongr
        exact hQpow _
      _ = 56000 * R ^ 2 * U ^ r := by ring
  have hT3 :
      |2 * (s : ℝ) * (r : ℝ) * Q ^ (s - 1) * QR * M ^ (r - 1) * V| ≤
        28672 * R ^ 2 * U ^ r := by
    by_cases hr0 : r = 0
    · simp [hr0]
      exact sq_nonneg R
    · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
      have hmix : M ^ (r - 1) * U ≤ U ^ r := by
        calc
          M ^ (r - 1) * U ≤ U ^ (r - 1) * U :=
            mul_le_mul_of_nonneg_right (hMpow (r - 1)) hU0
          _ = U ^ r := by rw [← pow_succ]; congr 1; omega
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity),
        abs_of_nonneg (pow_nonneg hQ0 _), abs_of_nonneg (pow_nonneg hM0 _)]
      calc
        _ ≤ 32 * 1 * (112 * R) * M ^ (r - 1) * (8 * R * U) := by
          gcongr
          exact hQpow _
        _ = 28672 * R ^ 2 * (M ^ (r - 1) * U) := by ring
        _ ≤ 28672 * R ^ 2 * U ^ r :=
          mul_le_mul_of_nonneg_left hmix (by positivity)
  have hT4 :
      |(((r * (r - 1) : ℕ) : ℝ) * Q ^ s * M ^ (r - 2) * V ^ 2)| ≤
        768 * R ^ 2 * U ^ r := by
    by_cases hr2 : 2 ≤ r
    · have hmix : M ^ (r - 2) * U ^ 2 ≤ U ^ r := by
        calc
          M ^ (r - 2) * U ^ 2 ≤ U ^ (r - 2) * U ^ 2 :=
            mul_le_mul_of_nonneg_right (hMpow (r - 2)) (sq_nonneg U)
          _ = U ^ r := by rw [← pow_add]; congr 1; omega
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity),
        abs_of_nonneg (pow_nonneg hQ0 _), abs_of_nonneg (pow_nonneg hM0 _), abs_pow]
      have hVsq : |V| ^ 2 ≤ (8 * R * U) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hV 2
      calc
        _ ≤ 12 * 1 * M ^ (r - 2) * (8 * R * U) ^ 2 := by
          gcongr
          exact hQpow _
        _ = 768 * R ^ 2 * (M ^ (r - 2) * U ^ 2) := by ring
        _ ≤ 768 * R ^ 2 * U ^ r :=
          mul_le_mul_of_nonneg_left hmix (by positivity)
    · have hrsmall : r = 0 ∨ r = 1 := by omega
      rcases hrsmall with hzero | hone
      · simp [hzero]
        exact sq_nonneg R
      · simp [hone]
        exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg R)) hU0
  rw [abs_mul, abs_of_nonneg hchoose0]
  have hcore : |rawCore Q M QR QC V j s| ≤ 235968 * R ^ 2 * U ^ r := by
    unfold rawCore
    calc
      _ ≤ |(((s * (s - 1) : ℕ) : ℝ) * Q ^ (s - 2) * QR ^ 2 * M ^ r)| +
          |(s : ℝ) * Q ^ (s - 1) * QC * M ^ r| +
          |2 * (s : ℝ) * (r : ℝ) * Q ^ (s - 1) * QR * M ^ (r - 1) * V| +
          |(((r * (r - 1) : ℕ) : ℝ) * Q ^ s * M ^ (r - 2) * V ^ 2)| := by
        calc
          _ ≤ |(((s * (s - 1) : ℕ) : ℝ) * Q ^ (s - 2) * QR ^ 2 * M ^ r) +
                (s : ℝ) * Q ^ (s - 1) * QC * M ^ r +
                2 * (s : ℝ) * (r : ℝ) * Q ^ (s - 1) * QR * M ^ (r - 1) * V| +
              |(((r * (r - 1) : ℕ) : ℝ) * Q ^ s * M ^ (r - 2) * V ^ 2)| :=
            abs_add_le _ _
          _ ≤ (|(((s * (s - 1) : ℕ) : ℝ) * Q ^ (s - 2) * QR ^ 2 * M ^ r) +
                  (s : ℝ) * Q ^ (s - 1) * QC * M ^ r| +
                |2 * (s : ℝ) * (r : ℝ) * Q ^ (s - 1) * QR * M ^ (r - 1) * V|) +
              |(((r * (r - 1) : ℕ) : ℝ) * Q ^ s * M ^ (r - 2) * V ^ 2)| := by
            have habc := abs_add_le
              ((((s * (s - 1) : ℕ) : ℝ) * Q ^ (s - 2) * QR ^ 2 * M ^ r) +
                (s : ℝ) * Q ^ (s - 1) * QC * M ^ r)
              (2 * (s : ℝ) * (r : ℝ) * Q ^ (s - 1) * QR * M ^ (r - 1) * V)
            linarith
          _ ≤ ((|(((s * (s - 1) : ℕ) : ℝ) * Q ^ (s - 2) * QR ^ 2 * M ^ r)| +
                  |(s : ℝ) * Q ^ (s - 1) * QC * M ^ r|) +
                |2 * (s : ℝ) * (r : ℝ) * Q ^ (s - 1) * QR * M ^ (r - 1) * V|) +
              |(((r * (r - 1) : ℕ) : ℝ) * Q ^ s * M ^ (r - 2) * V ^ 2)| := by
            have hab := abs_add_le
              (((s * (s - 1) : ℕ) : ℝ) * Q ^ (s - 2) * QR ^ 2 * M ^ r)
              ((s : ℝ) * Q ^ (s - 1) * QC * M ^ r)
            linarith
      _ ≤ 150528 * R ^ 2 * U ^ r + 56000 * R ^ 2 * U ^ r +
          28672 * R ^ 2 * U ^ r + 768 * R ^ 2 * U ^ r :=
        add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4
      _ = 235968 * R ^ 2 * U ^ r := by ring
  calc
    (Nat.choose j s : ℝ) * |rawCore Q M QR QC V j s| ≤
        6 * (235968 * R ^ 2 * U ^ r) := by gcongr
    _ ≤ 2000000 * R ^ 2 * U ^ r := by
      have : 0 ≤ R ^ 2 * U ^ r := by positivity
      nlinarith

def rawRateCore (Q M QR V : ℝ) (j s : ℕ) : ℝ :=
  (s : ℝ) * Q ^ (s - 1) * QR * M ^ (j - s) +
    Q ^ s * ((j - s : ℕ) : ℝ) * M ^ (j - s - 1) * V

theorem rawRateCore_bound {Q M QR V U R : ℝ} {j s : ℕ}
    (hsj : s ≤ j) (hj : j ≤ 4)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hM0 : 0 ≤ M) (hM1 : M ≤ U)
    (hU0 : 0 ≤ U) (hR0 : 0 ≤ R)
    (hQR : |QR| ≤ 112 * R) (hV : |V| ≤ 8 * R * U) :
    |(Nat.choose j s : ℝ) * rawRateCore Q M QR V j s| ≤
      3000 * R * U ^ (j - s) := by
  have hs4 : (s : ℝ) ≤ 4 := by exact_mod_cast hsj.trans hj
  have hr4 : ((j - s : ℕ) : ℝ) ≤ 4 := by
    exact_mod_cast (Nat.sub_le j s).trans hj
  have hchoose0 : 0 ≤ (Nat.choose j s : ℝ) := by positivity
  have hchoose6 : (Nat.choose j s : ℝ) ≤ 6 := by
    exact_mod_cast choose_le_six hsj hj
  have hQpow (n : ℕ) : Q ^ n ≤ 1 := pow_le_one₀ hQ0 hQ1
  have hMpow (n : ℕ) : M ^ n ≤ U ^ n := pow_le_pow_left₀ hM0 hM1 n
  let r := j - s
  have hT1 : |(s : ℝ) * Q ^ (s - 1) * QR * M ^ r| ≤
      448 * R * U ^ r := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity),
      abs_of_nonneg (pow_nonneg hQ0 _), abs_of_nonneg (pow_nonneg hM0 _)]
    calc
      _ ≤ 4 * 1 * (112 * R) * U ^ r := by
        gcongr
        exact hQpow _
      _ = 448 * R * U ^ r := by ring
  have hT2 : |Q ^ s * (r : ℝ) * M ^ (r - 1) * V| ≤
      32 * R * U ^ r := by
    by_cases hr0 : r = 0
    · simp [hr0, hR0]
    · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
      have hmix : M ^ (r - 1) * U ≤ U ^ r := by
        calc
          M ^ (r - 1) * U ≤ U ^ (r - 1) * U :=
            mul_le_mul_of_nonneg_right (hMpow (r - 1)) hU0
          _ = U ^ r := by rw [← pow_succ]; congr 1; omega
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hQ0 _),
        abs_of_nonneg (by positivity), abs_of_nonneg (pow_nonneg hM0 _)]
      calc
        _ ≤ 1 * 4 * M ^ (r - 1) * (8 * R * U) := by
          gcongr
          exact hQpow _
        _ = 32 * R * (M ^ (r - 1) * U) := by ring
        _ ≤ 32 * R * U ^ r :=
          mul_le_mul_of_nonneg_left hmix (by positivity)
  rw [abs_mul, abs_of_nonneg hchoose0]
  have hcore : |rawRateCore Q M QR V j s| ≤ 480 * R * U ^ r := by
    unfold rawRateCore
    exact (abs_add_le _ _).trans (by linarith)
  calc
    (Nat.choose j s : ℝ) * |rawRateCore Q M QR V j s| ≤
        6 * (480 * R * U ^ r) := by gcongr
    _ ≤ 3000 * R * U ^ r := by
      have : 0 ≤ R * U ^ r := by positivity
      nlinarith

theorem zHatCurvature_bound_source {D₂ D₃ D₄ Gamma d N x : ℝ} {j s : ℕ}
    (hd : 1 ≤ d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hpV : 0 < pV N x) (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) (hsj : s ≤ j) (hj : j ≤ 4) :
    |zHatCurvature D₂ D₃ D₄ d N j s x| ≤
      2000000 * (Gamma / (N * pV N x)) ^ 2 * (d⁻¹) ^ (j - s) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  rw [zHatCurvature_eq_raw hdpos hN hpV hsj hj]
  change |(Nat.choose j s : ℝ) * rawCore
      (q D₂ D₃ D₄ d N x) (pM d N x) (qRate D₂ D₃ D₄ d N x)
      (qCurvature D₂ D₃ D₄ d N x) (8 / (d * N)) j s| ≤ _
  apply rawCore_bound hsj hj (q_pos hpV).le
  · exact q_le_one hpV.le hpV1 (GammaHat_nonneg hD₂0 hD₃0 hD₄0 hpM0)
  · exact hpM0
  · exact hpM1
  · exact inv_nonneg.mpr hdpos.le
  · positivity
  · convert qRate_bound hdpos hN hGamma hpV hpV1 hpM0 hpM1
      hD₂0 hD₃0 hD₄0 hD₂ hD₃ hD₄ using 1 <;> ring
  · convert qCurvature_bound hdpos hN hGamma hpV hpV1 hpM0 hpM1
      hD₂0 hD₃0 hD₄0 hD₂ hD₃ hD₄ using 1 <;> ring
  · rw [abs_of_nonneg (by positivity : 0 ≤ 8 / (d * N))]
    have hden : 0 < N * pV N x := mul_pos hN hpV
    have hone : 1 / N ≤ Gamma / (N * pV N x) := by
      calc
        1 / N = pV N x / (N * pV N x) := by field_simp
        _ ≤ Gamma / (N * pV N x) :=
          div_le_div_of_nonneg_right (hpV1.trans hGamma) hden.le
    calc
      8 / (d * N) = 8 * (1 / N) * d⁻¹ := by field_simp
      _ ≤ 8 * (Gamma / (N * pV N x)) * d⁻¹ := by gcongr

theorem zHatCurvature_bound_floor {D₂ D₃ D₄ Gamma d N x P : ℝ} {j s : ℕ}
    (hd : 1 ≤ d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hP : 0 < P) (hPfloor : P ≤ pV N x)
    (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) (hsj : s ≤ j) (hj : j ≤ 4) :
    |zHatCurvature D₂ D₃ D₄ d N j s x| ≤
      2000000 * (Gamma / (N * P)) ^ 2 * (d⁻¹) ^ (j - s) := by
  have hpV : 0 < pV N x := hP.trans_le hPfloor
  have hpoint := zHatCurvature_bound_source hd hN hGamma hpV hpV1 hpM0 hpM1
    hD₂0 hD₃0 hD₄0 hD₂ hD₃ hD₄ hsj hj
  have hGamma0 : 0 ≤ Gamma := by linarith
  have hdenP : 0 < N * P := mul_pos hN hP
  have hdenPV : 0 < N * pV N x := mul_pos hN hpV
  have hdenle : N * P ≤ N * pV N x :=
    mul_le_mul_of_nonneg_left hPfloor hN.le
  have hR : Gamma / (N * pV N x) ≤ Gamma / (N * P) :=
    div_le_div_of_nonneg_left hGamma0 hdenP hdenle
  have hR0 : 0 ≤ Gamma / (N * pV N x) := div_nonneg hGamma0 hdenPV.le
  have hRsq : (Gamma / (N * pV N x)) ^ 2 ≤ (Gamma / (N * P)) ^ 2 :=
    pow_le_pow_left₀ hR0 hR 2
  calc
    _ ≤ 2000000 * (Gamma / (N * pV N x)) ^ 2 * (d⁻¹) ^ (j - s) := hpoint
    _ ≤ 2000000 * (Gamma / (N * P)) ^ 2 * (d⁻¹) ^ (j - s) := by gcongr

/-- Pure numeric absorption condition for the bare test curvature. -/
def zHatLargeDCondition (Gamma epsilon d N P : ℝ) (j s : ℕ) : Prop :=
  2000000 * (Gamma / (N * P)) ^ 2 * (d⁻¹) ^ (j - s) ≤
    d ^ ((s : ℝ) - j - epsilon) / N

theorem zHatCurvature_largeD {D₂ D₃ D₄ Gamma epsilon d N x P : ℝ} {j s : ℕ}
    (hd : 1 ≤ d) (hN : 0 < N) (hGamma : 1 ≤ Gamma)
    (hP : 0 < P) (hPfloor : P ≤ pV N x)
    (hpV1 : pV N x ≤ 1)
    (hpM0 : 0 ≤ pM d N x) (hpM1 : pM d N x ≤ d⁻¹)
    (hD₂0 : 0 ≤ D₂) (hD₃0 : 0 ≤ D₃) (hD₄0 : 0 ≤ D₄)
    (hD₂ : D₂ ≤ Gamma * d) (hD₃ : D₃ ≤ Gamma * d ^ 2)
    (hD₄ : D₄ ≤ Gamma * d ^ 3) (hsj : s ≤ j) (hj : j ≤ 4)
    (hlarge : zHatLargeDCondition Gamma epsilon d N P j s) :
    |zHatCurvature D₂ D₃ D₄ d N j s x| ≤
      d ^ ((s : ℝ) - j - epsilon) / N :=
  (zHatCurvature_bound_floor hd hN hGamma hP hPfloor hpV1 hpM0 hpM1
    hD₂0 hD₃0 hD₄0 hD₂ hD₃ hD₄ hsj hj).trans hlarge

def correction (D₂ D₃ D₄ Gamma d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose j s : ℝ) * dHat D₂ D₃ D₄ d N x ^ s / (4 * Gamma * d ^ j)

def correctionRate (D₂ D₃ D₄ Gamma d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose j s : ℝ) * (s : ℝ) * dHat D₂ D₃ D₄ d N x ^ (s - 1) *
    degreeRate D₂ D₃ D₄ d N x / (4 * Gamma * d ^ j)

def correctionCurvature (D₂ D₃ D₄ Gamma d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose j s : ℝ) * (s : ℝ) *
    (((s - 1 : ℕ) : ℝ) * dHat D₂ D₃ D₄ d N x ^ (s - 2) *
        degreeRate D₂ D₃ D₄ d N x ^ 2 +
      dHat D₂ D₃ D₄ d N x ^ (s - 1) *
        degreeCurvature D₂ D₃ D₄ d N x) /
    (4 * Gamma * d ^ j)

def testInsideRate2 (D₂ D₃ D₄ Gamma d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  zHatRate D₂ D₃ D₄ d N j s x + correctionRate D₂ D₃ D₄ Gamma d N j s x

def testInsideCurvature2 (D₂ D₃ D₄ Gamma d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  zHatCurvature D₂ D₃ D₄ d N j s x + correctionCurvature D₂ D₃ D₄ Gamma d N j s x

def zetaCurvatureFormula (D₂ D₃ D₄ Gamma epsilon d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  (gamma Gamma N x ^ 2 + gammaSlope Gamma N x) * xi Gamma epsilon d N x *
      testInside D₂ D₃ D₄ Gamma d N j s x +
    2 * gamma Gamma N x * xi Gamma epsilon d N x *
      testInsideRate2 D₂ D₃ D₄ Gamma d N j s x +
    xi Gamma epsilon d N x * testInsideCurvature2 D₂ D₃ D₄ Gamma d N j s x

theorem hasDerivAt_correction {D₂ D₃ D₄ Gamma d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 < Gamma) (hpV : 0 < pV N x) :
    HasDerivAt (correction D₂ D₃ D₄ Gamma d N j s)
      (correctionRate D₂ D₃ D₄ Gamma d N j s x) x := by
  have h := (((hasDerivAt_dHat_degreeRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    hd hN hpV).pow s).const_mul (Nat.choose j s : ℝ)).div_const (4 * Gamma * d ^ j)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [correction, Pi.mul_apply, Pi.pow_apply]
  · simp only [correctionRate, Pi.mul_apply, Pi.pow_apply]
    ring

theorem hasDerivAt_correctionRate {D₂ D₃ D₄ Gamma d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 < Gamma) (hpV : 0 < pV N x) :
    HasDerivAt (correctionRate D₂ D₃ D₄ Gamma d N j s)
      (correctionCurvature D₂ D₃ D₄ Gamma d N j s x) x := by
  have h := (((hasDerivAt_dHat_degreeRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    hd hN hpV).pow (s - 1)).mul
      (hasDerivAt_degreeRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hN hpV)).const_mul
        ((Nat.choose j s : ℝ) * (s : ℝ) / (4 * Gamma * d ^ j))
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [correctionRate, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [correctionCurvature, Pi.mul_apply, Pi.pow_apply]
    cases s with
    | zero => simp
    | succ s =>
      cases s with
      | zero => simp; ring
      | succ s =>
        simp only [Nat.cast_succ, Nat.succ_sub_one, Nat.succ_sub_succ_eq_sub,
          Nat.sub_zero, Nat.add_sub_cancel]
        ring

theorem hasDerivAt_testInside2 {D₂ D₃ D₄ Gamma d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 < Gamma) (hpV : 0 < pV N x)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    HasDerivAt (testInside D₂ D₃ D₄ Gamma d N j s)
      (testInsideRate2 D₂ D₃ D₄ Gamma d N j s x) x := by
  have h := (hasDerivAt_zHat_rate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    hd hN hpV hsj hj).add
      (hasDerivAt_correction (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) (j := j) (s := s)
        hd hN hGamma hpV)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [testInside, correction, Pi.add_apply]
  · simp only [testInsideRate2]

theorem hasDerivAt_testInsideRate2 {D₂ D₃ D₄ Gamma d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 < Gamma) (hpV : 0 < pV N x) :
    HasDerivAt (testInsideRate2 D₂ D₃ D₄ Gamma d N j s)
      (testInsideCurvature2 D₂ D₃ D₄ Gamma d N j s x) x := by
  have h := (hasDerivAt_zHatRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    (j := j) (s := s) hd hN hpV).add
      (hasDerivAt_correctionRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) (j := j) (s := s)
        hd hN hGamma hpV)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [testInsideRate2, Pi.add_apply]
  · simp only [testInsideCurvature2]

def zetaProductRate (D₂ D₃ D₄ Gamma epsilon d N : ℝ) (j s : ℕ) (x : ℝ) : ℝ :=
  gamma Gamma N x * xi Gamma epsilon d N x *
      testInside D₂ D₃ D₄ Gamma d N j s x +
    xi Gamma epsilon d N x * testInsideRate2 D₂ D₃ D₄ Gamma d N j s x

theorem hasDerivAt_zetaProductRate {D₂ D₃ D₄ Gamma epsilon d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 < Gamma) (hpV : 0 < pV N x)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    HasDerivAt (zetaProductRate D₂ D₃ D₄ Gamma epsilon d N j s)
      (zetaCurvatureFormula D₂ D₃ D₄ Gamma epsilon d N j s x) x := by
  have hgammaxi := (hasDerivAt_gamma (Gamma := Gamma) hN hpV).mul
    (hasDerivAt_xi (Gamma := Gamma) (epsilon := epsilon) hd hpV)
  have hleft := hgammaxi.mul
    (hasDerivAt_testInside2 (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
      hd hN hGamma hpV hsj hj)
  have hright := (hasDerivAt_xi (Gamma := Gamma) (epsilon := epsilon) hd hpV).mul
    (hasDerivAt_testInsideRate2 (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
      (j := j) (s := s) hd hN hGamma hpV)
  have h := hleft.add hright
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [zetaProductRate, Pi.add_apply, Pi.mul_apply]
  · simp only [zetaCurvatureFormula, Pi.add_apply, Pi.mul_apply]
    ring

theorem hasDerivAt_zeta_product {D₂ D₃ D₄ Gamma epsilon d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 < Gamma) (hpV : 0 < pV N x)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    HasDerivAt (zeta D₂ D₃ D₄ Gamma epsilon d N j s)
      (zetaProductRate D₂ D₃ D₄ Gamma epsilon d N j s x) x := by
  have h := (hasDerivAt_xi (Gamma := Gamma) (epsilon := epsilon) hd hpV).mul
    (hasDerivAt_testInside2 (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
      hd hN hGamma hpV hsj hj)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [zeta, testInside, Pi.mul_apply]
  · simp only [zetaProductRate, Pi.mul_apply]

theorem zetaCurvature_eq_formula {D₂ D₃ D₄ Gamma epsilon d N x : ℝ} {j s : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hGamma : 0 < Gamma) (hpV : 0 < pV N x)
    (hsj : s ≤ j) (hj : j ≤ 4) :
    zetaCurvature D₂ D₃ D₄ Gamma epsilon d N j s x =
      zetaCurvatureFormula D₂ D₃ D₄ Gamma epsilon d N j s x := by
  have hev : ∀ᶠ y in nhds x, 0 < pV N y :=
    (hasDerivAt_pV N x).continuousAt.eventually (Ioi_mem_nhds hpV)
  have heq : zetaRate D₂ D₃ D₄ Gamma epsilon d N j s =ᶠ[nhds x]
      zetaProductRate D₂ D₃ D₄ Gamma epsilon d N j s := by
    filter_upwards [hev] with y hy
    exact (hasDerivAt_zeta_rate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
      hd hN hGamma hy hsj hj).unique
        (hasDerivAt_zeta_product (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
          hd hN hGamma hy hsj hj)
  have h := (hasDerivAt_zetaProductRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    hd hN hGamma hpV hsj hj).congr_of_eventuallyEq heq
  exact (hasDerivAt_zetaRate (D₂ := D₂) (D₃ := D₃) (D₄ := D₄)
    (j := j) (s := s) hd hN hGamma hpV).unique h

theorem zetaCurvatureFormula_bound
    {D₂ D₃ D₄ Gamma epsilon d N x X U V W G H : ℝ} {j s : ℕ}
    (hX : 0 ≤ X) (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hxi : |xi Gamma epsilon d N x| ≤ X)
    (hin : |testInside D₂ D₃ D₄ Gamma d N j s x| ≤ U)
    (hrate : |testInsideRate2 D₂ D₃ D₄ Gamma d N j s x| ≤ V)
    (hcurv : |testInsideCurvature2 D₂ D₃ D₄ Gamma d N j s x| ≤ W)
    (hgamma : |gamma Gamma N x| ≤ G) (hslope : |gammaSlope Gamma N x| ≤ H) :
    |zetaCurvatureFormula D₂ D₃ D₄ Gamma epsilon d N j s x| ≤
      (G ^ 2 + H) * X * U + 2 * G * X * V + X * W := by
  have hgsq : |gamma Gamma N x| ^ 2 ≤ G ^ 2 := by
    simpa only [pow_two] using
      mul_self_le_mul_self (abs_nonneg (gamma Gamma N x)) hgamma
  have hcoef : |gamma Gamma N x ^ 2 + gammaSlope Gamma N x| ≤ G ^ 2 + H := by
    calc
      _ ≤ |gamma Gamma N x ^ 2| + |gammaSlope Gamma N x| := abs_add_le _ _
      _ = |gamma Gamma N x| ^ 2 + |gammaSlope Gamma N x| := by rw [abs_pow]
      _ ≤ G ^ 2 + H := add_le_add hgsq hslope
  unfold zetaCurvatureFormula
  calc
    |(gamma Gamma N x ^ 2 + gammaSlope Gamma N x) * xi Gamma epsilon d N x *
          testInside D₂ D₃ D₄ Gamma d N j s x +
        2 * gamma Gamma N x * xi Gamma epsilon d N x *
          testInsideRate2 D₂ D₃ D₄ Gamma d N j s x +
        xi Gamma epsilon d N x *
          testInsideCurvature2 D₂ D₃ D₄ Gamma d N j s x| ≤
      |(gamma Gamma N x ^ 2 + gammaSlope Gamma N x) * xi Gamma epsilon d N x *
          testInside D₂ D₃ D₄ Gamma d N j s x| +
        |2 * gamma Gamma N x * xi Gamma epsilon d N x *
          testInsideRate2 D₂ D₃ D₄ Gamma d N j s x| +
        |xi Gamma epsilon d N x *
          testInsideCurvature2 D₂ D₃ D₄ Gamma d N j s x| := by
            simpa only [add_assoc] using
              (abs_add_three
                ((gamma Gamma N x ^ 2 + gammaSlope Gamma N x) * xi Gamma epsilon d N x *
                  testInside D₂ D₃ D₄ Gamma d N j s x)
                (2 * gamma Gamma N x * xi Gamma epsilon d N x *
                  testInsideRate2 D₂ D₃ D₄ Gamma d N j s x)
                (xi Gamma epsilon d N x *
                  testInsideCurvature2 D₂ D₃ D₄ Gamma d N j s x))
    _ = |gamma Gamma N x ^ 2 + gammaSlope Gamma N x| *
          |xi Gamma epsilon d N x| *
          |testInside D₂ D₃ D₄ Gamma d N j s x| +
        2 * |gamma Gamma N x| * |xi Gamma epsilon d N x| *
          |testInsideRate2 D₂ D₃ D₄ Gamma d N j s x| +
        |xi Gamma epsilon d N x| *
          |testInsideCurvature2 D₂ D₃ D₄ Gamma d N j s x| := by
            simp only [abs_mul]
            norm_num
    _ ≤ (G ^ 2 + H) * X * U + 2 * G * X * V + X * W := by
      gcongr

def testScale (d : ℝ) (j s : ℕ) : ℝ := (d⁻¹) ^ (j - s)

theorem degreeRate_bound_at_step
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ}
    (R : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (hy : y ∈ Icc x (x + 1)) :
    |degreeRate D₂ D₃ D₄ d N y| ≤ 104 * Gamma * d / (N * P) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.d_one
  have hGamma0 : 0 ≤ Gamma := by linarith [R.Gamma_one]
  have hpV := pV_pos R.N_pos (R.before_end y hy)
  have hpV1 := pV_le_one R.N_pos (R.time_nonneg y hy)
  have hpM0 := pM_nonneg hd R.N_pos (R.time_nonneg y hy)
  have hpM1 := pM_le_inv hd R.N_pos (R.before_end y hy).le
  have hGH := GammaHat_nonneg R.D₂_nonneg R.D₃_nonneg R.D₄_nonneg hpM0
  have hdHat0 := (dHat_pos (D₂ := D₂) (D₃ := D₃) (D₄ := D₄) hd hpV).le
  have hdHat := dHat_le_d hd.le hpV.le hpV1 hGH
  have hA0 := degreeHazard_nonneg hd R.N_pos hpV R.D₂_nonneg R.D₃_nonneg R.D₄_nonneg hpM0
  have hA := degreeHazard_le hd R.N_pos R.Gamma_one hpV hpV1 hpM0 hpM1
    R.D₂_bound R.D₃_bound R.D₄_bound
  have hNP : 0 < N * P := mul_pos R.N_pos R.P_pos
  have hNpV : 0 < N * pV N y := mul_pos R.N_pos hpV
  have hNPle : N * P ≤ N * pV N y :=
    mul_le_mul_of_nonneg_left (R.pV_floor y hy) R.N_pos.le
  have hA' : degreeHazard D₂ D₃ D₄ d N y ≤ 104 * Gamma / (N * P) := by
    apply hA.trans
    rw [div_le_div_iff₀ hNpV hNP]
    exact mul_le_mul_of_nonneg_left hNPle (mul_nonneg (by norm_num) hGamma0)
  unfold degreeRate
  rw [abs_mul, abs_neg, abs_of_nonneg hA0, abs_of_nonneg hdHat0]
  calc
    degreeHazard D₂ D₃ D₄ d N y * dHat D₂ D₃ D₄ d N y ≤
        (104 * Gamma / (N * P)) * d :=
      mul_le_mul hA' hdHat hdHat0 (div_nonneg (by positivity) hNP.le)
    _ = 104 * Gamma * d / (N * P) := by ring

theorem degreeCurvature_bound_at_step
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ}
    (R : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (hy : y ∈ Icc x (x + 1)) :
    |degreeCurvature D₂ D₃ D₄ d N y| ≤
      12000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.d_one
  have hpV := pV_pos R.N_pos (R.before_end y hy)
  have hpV1 := pV_le_one R.N_pos (R.time_nonneg y hy)
  have hpM0 := pM_nonneg hd R.N_pos (R.time_nonneg y hy)
  have hpM1 := pM_le_inv hd R.N_pos (R.before_end y hy).le
  have hpoint := degreeCurvature_bound hd R.N_pos R.Gamma_one hpV hpV1 hpM0 hpM1
    R.D₂_nonneg R.D₃_nonneg R.D₄_nonneg R.D₂_bound R.D₃_bound R.D₄_bound
  have hP2 : P ^ 2 ≤ pV N y ^ 2 := by
    nlinarith [mul_self_le_mul_self R.P_pos.le (R.pV_floor y hy)]
  have hdenP : 0 < N ^ 2 * P ^ 2 := mul_pos (sq_pos_of_pos R.N_pos) (sq_pos_of_pos R.P_pos)
  have hdenV : 0 < N ^ 2 * pV N y ^ 2 := mul_pos (sq_pos_of_pos R.N_pos) (sq_pos_of_pos hpV)
  apply hpoint.trans
  rw [div_le_div_iff₀ hdenV hdenP]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hP2 (sq_nonneg N)) (by positivity)

theorem zHatRate_bound_at_step
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ} {j s : ℕ}
    (R : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (hy : y ∈ Icc x (x + 1)) (hsj : s ≤ j) (hj : j ≤ 4) :
    |zHatRate D₂ D₃ D₄ d N j s y| ≤
      3000 * Gamma * testScale d j s / (N * P) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.d_one
  have hGamma0 : 0 ≤ Gamma := by linarith [R.Gamma_one]
  have hpV := pV_pos R.N_pos (R.before_end y hy)
  have hpV1 := pV_le_one R.N_pos (R.time_nonneg y hy)
  have hpM0 := pM_nonneg hd R.N_pos (R.time_nonneg y hy)
  have hpM1 := pM_le_inv hd R.N_pos (R.before_end y hy).le
  have hGH := GammaHat_nonneg R.D₂_nonneg R.D₃_nonneg R.D₄_nonneg hpM0
  have hNP : 0 < N * P := mul_pos R.N_pos R.P_pos
  have hNpV : 0 < N * pV N y := mul_pos R.N_pos hpV
  have hNPle : N * P ≤ N * pV N y :=
    mul_le_mul_of_nonneg_left (R.pV_floor y hy) R.N_pos.le
  have hR : Gamma / (N * pV N y) ≤ Gamma / (N * P) :=
    div_le_div_of_nonneg_left hGamma0 hNP hNPle
  have hqrate : |qRate D₂ D₃ D₄ d N y| ≤ 112 * (Gamma / (N * P)) := by
    calc
      _ ≤ 112 * Gamma / (N * pV N y) :=
        qRate_bound hd R.N_pos R.Gamma_one hpV hpV1 hpM0 hpM1
          R.D₂_nonneg R.D₃_nonneg R.D₄_nonneg R.D₂_bound R.D₃_bound R.D₄_bound
      _ = 112 * (Gamma / (N * pV N y)) := by ring
      _ ≤ 112 * (Gamma / (N * P)) := mul_le_mul_of_nonneg_left hR (by norm_num)
  rw [zHatRate_eq_rawRate hd R.N_pos hpV hsj hj]
  have hV : |8 / (d * N)| ≤ 8 * (Gamma / (N * P)) * d⁻¹ := by
    rw [abs_of_nonneg (div_nonneg (by norm_num)
      (mul_nonneg hd.le R.N_pos.le))]
    have hP1 : P ≤ 1 := (R.pV_floor y hy).trans hpV1
    have hone : 1 / N ≤ Gamma / (N * P) := by
      calc
        1 / N = P / (N * P) := by
          field_simp [ne_of_gt R.N_pos, ne_of_gt R.P_pos]
        _ ≤ Gamma / (N * P) :=
          div_le_div_of_nonneg_right (hP1.trans R.Gamma_one) hNP.le
    calc
      8 / (d * N) = 8 * (1 / N) * d⁻¹ := by field_simp
      _ ≤ 8 * (Gamma / (N * P)) * d⁻¹ := by gcongr
  have hraw := rawRateCore_bound
    (Q := q D₂ D₃ D₄ d N y) (M := pM d N y)
    (QR := qRate D₂ D₃ D₄ d N y) (V := 8 / (d * N))
    (U := d⁻¹) (R := Gamma / (N * P)) hsj hj (q_pos hpV).le
    (q_le_one hpV.le hpV1 hGH) hpM0 hpM1 (inv_nonneg.mpr hd.le)
    (div_nonneg hGamma0 hNP.le) hqrate hV
  calc
    |zHatRawRate D₂ D₃ D₄ d N j s y| =
        |(Nat.choose j s : ℝ) * rawRateCore
          (q D₂ D₃ D₄ d N y) (pM d N y) (qRate D₂ D₃ D₄ d N y)
          (8 / (d * N)) j s| := by
      congr 1
      unfold zHatRawRate rawRateCore
      ring
    _ ≤ 3000 * (Gamma / (N * P)) * (d⁻¹) ^ (j - s) := hraw
    _ = 3000 * Gamma * testScale d j s / (N * P) := by
      unfold testScale
      field_simp [ne_of_gt R.N_pos, ne_of_gt R.P_pos]

theorem correctionRate_bound_at_step
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ} {j s : ℕ}
    (R : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (hy : y ∈ Icc x (x + 1)) (hsj : s ≤ j) (hj : j ≤ 4) :
    |correctionRate D₂ D₃ D₄ Gamma d N j s y| ≤
      2000 * Gamma * testScale d j s / (N * P) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.d_one
  have hGamma : 0 < Gamma := lt_of_lt_of_le (by norm_num) R.Gamma_one
  have hpV := pV_pos R.N_pos (R.before_end y hy)
  have hpV1 := pV_le_one R.N_pos (R.time_nonneg y hy)
  have hpM0 := pM_nonneg hd R.N_pos (R.time_nonneg y hy)
  have hGH := GammaHat_nonneg R.D₂_nonneg R.D₃_nonneg R.D₄_nonneg hpM0
  have hu0 : 0 ≤ dHat D₂ D₃ D₄ d N y := (dHat_pos hd hpV).le
  have hu : dHat D₂ D₃ D₄ d N y ≤ d := dHat_le_d hd.le hpV.le hpV1 hGH
  have hr := degreeRate_bound_at_step R hy
  have hNP : 0 < N * P := mul_pos R.N_pos R.P_pos
  by_cases hs0 : s = 0
  · subst s
    unfold correctionRate testScale
    norm_num
    exact div_nonneg (by positivity) hNP.le
  have hspos : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
  have hupow : dHat D₂ D₃ D₄ d N y ^ (s - 1) ≤ d ^ (s - 1) :=
    pow_le_pow_left₀ hu0 hu _
  have hchoose : (Nat.choose j s : ℝ) * (s : ℝ) ≤ 64 := by
    interval_cases j <;> interval_cases s <;> norm_num [Nat.choose]
  have hden : 0 < 4 * Gamma * d ^ j := by positivity
  have hpow : d ^ (s - 1) * d = d ^ s := by
    rw [← pow_succ]
    congr 1
    omega
  have hscale : d ^ s / d ^ j = testScale d j s := by
    unfold testScale
    rw [inv_pow, show d ^ j = d ^ s * d ^ (j - s) by
      rw [← pow_add]; congr 1; omega]
    field_simp
  unfold correctionRate
  rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (Nat.choose j s : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ (s : ℝ)),
    abs_of_nonneg (pow_nonneg hu0 _)]
  calc
    (Nat.choose j s : ℝ) * (s : ℝ) * dHat D₂ D₃ D₄ d N y ^ (s - 1) *
          |degreeRate D₂ D₃ D₄ d N y| / (4 * Gamma * d ^ j) ≤
        64 * d ^ (s - 1) * (104 * Gamma * d / (N * P)) /
          (4 * Gamma * d ^ j) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul hchoose hupow (pow_nonneg hu0 _) (by norm_num)) hr
          (abs_nonneg _) (by positivity)) hden.le
    _ = 1664 * (d ^ s / d ^ j) / (N * P) := by
      rw [← hpow]
      field_simp
      ring
    _ = 1664 * testScale d j s / (N * P) := by rw [hscale]
    _ ≤ 2000 * Gamma * testScale d j s / (N * P) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by nlinarith [R.Gamma_one])
          (pow_nonneg (inv_nonneg.mpr hd.le) _)) hNP.le

theorem testInsideRate_bound_at_step
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ} {j s : ℕ}
    (R : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (hy : y ∈ Icc x (x + 1)) (hsj : s ≤ j) (hj : j ≤ 4) :
    |testInsideRate2 D₂ D₃ D₄ Gamma d N j s y| ≤
      5000 * Gamma * d ^ ((s : ℝ) - j) / (N * P) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.d_one
  have hscale : testScale d j s = d ^ ((s : ℝ) - j) :=
    inv_pow_eq_rpow_sub hd hsj
  unfold testInsideRate2
  calc
    |zHatRate D₂ D₃ D₄ d N j s y + correctionRate D₂ D₃ D₄ Gamma d N j s y| ≤
        |zHatRate D₂ D₃ D₄ d N j s y| +
          |correctionRate D₂ D₃ D₄ Gamma d N j s y| := abs_add_le _ _
    _ ≤ 3000 * Gamma * testScale d j s / (N * P) +
        2000 * Gamma * testScale d j s / (N * P) :=
      add_le_add (zHatRate_bound_at_step R hy hsj hj)
        (correctionRate_bound_at_step R hy hsj hj)
    _ = 5000 * Gamma * d ^ ((s : ℝ) - j) / (N * P) := by rw [hscale]; ring

theorem correctionCurvature_bound_at_step
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ} {j s : ℕ}
    (R : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (hy : y ∈ Icc x (x + 1)) (hsj : s ≤ j) (hj : j ≤ 4) :
    |correctionCurvature D₂ D₃ D₄ Gamma d N j s y| ≤
      1000000 * Gamma ^ 2 * testScale d j s / (N ^ 2 * P ^ 2) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.d_one
  have hGamma : 0 < Gamma := lt_of_lt_of_le (by norm_num) R.Gamma_one
  have hpV := pV_pos R.N_pos (R.before_end y hy)
  have hpV1 := pV_le_one R.N_pos (R.time_nonneg y hy)
  have hpM0 := pM_nonneg hd R.N_pos (R.time_nonneg y hy)
  have hGH := GammaHat_nonneg R.D₂_nonneg R.D₃_nonneg R.D₄_nonneg hpM0
  have hu0 : 0 ≤ dHat D₂ D₃ D₄ d N y := (dHat_pos hd hpV).le
  have hu : dHat D₂ D₃ D₄ d N y ≤ d := dHat_le_d hd.le hpV.le hpV1 hGH
  have hr := degreeRate_bound_at_step R hy
  have hc := degreeCurvature_bound_at_step R hy
  by_cases hs0 : s = 0
  · subst s
    unfold correctionCurvature testScale
    norm_num
    have hK : 0 < N ^ 2 * P ^ 2 :=
      mul_pos (sq_pos_of_pos R.N_pos) (sq_pos_of_pos R.P_pos)
    exact div_nonneg (by positivity) hK.le
  have hspos : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
  have hK : 0 < N ^ 2 * P ^ 2 :=
    mul_pos (sq_pos_of_pos R.N_pos) (sq_pos_of_pos R.P_pos)
  have hR2 : |degreeRate D₂ D₃ D₄ d N y ^ 2| ≤
      (104 * Gamma * d / (N * P)) ^ 2 := by
    rw [abs_pow]
    simpa only [pow_two] using
      mul_self_le_mul_self (abs_nonneg (degreeRate D₂ D₃ D₄ d N y)) hr
  have hUC : |dHat D₂ D₃ D₄ d N y * degreeCurvature D₂ D₃ D₄ d N y| ≤
      d * (12000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2)) := by
    rw [abs_mul, abs_of_nonneg hu0]
    exact mul_le_mul hu hc (abs_nonneg _) hd.le
  have hUR2 : |dHat D₂ D₃ D₄ d N y * degreeRate D₂ D₃ D₄ d N y ^ 2| ≤
      d * (104 * Gamma * d / (N * P)) ^ 2 := by
    rw [abs_mul]
    exact mul_le_mul (by simpa [abs_of_nonneg hu0] using hu) hR2 (abs_nonneg _) hd.le
  have hU2C : |dHat D₂ D₃ D₄ d N y ^ 2 * degreeCurvature D₂ D₃ D₄ d N y| ≤
      d ^ 2 * (12000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2)) := by
    rw [abs_mul, abs_pow, abs_of_nonneg hu0]
    exact mul_le_mul (pow_le_pow_left₀ hu0 hu 2) hc (abs_nonneg _) (sq_nonneg d)
  have hU2R2 : |dHat D₂ D₃ D₄ d N y ^ 2 * degreeRate D₂ D₃ D₄ d N y ^ 2| ≤
      d ^ 2 * (104 * Gamma * d / (N * P)) ^ 2 := by
    rw [abs_mul, abs_pow, abs_of_nonneg hu0]
    exact mul_le_mul (pow_le_pow_left₀ hu0 hu 2) hR2 (abs_nonneg _) (sq_nonneg d)
  let num : ℝ := (((s - 1 : ℕ) : ℝ) * dHat D₂ D₃ D₄ d N y ^ (s - 2) *
        degreeRate D₂ D₃ D₄ d N y ^ 2 +
      dHat D₂ D₃ D₄ d N y ^ (s - 1) * degreeCurvature D₂ D₃ D₄ d N y)
  have hs4 : s ≤ 4 := hsj.trans hj
  have hnum : |num| ≤ 45000 * Gamma ^ 2 * d ^ s / (N ^ 2 * P ^ 2) := by
    have hcases : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by omega
    rcases hcases with h | h | h | h <;> subst s <;>
      simp only [num, Nat.cast_one, Nat.cast_ofNat, Nat.reduceSub, pow_zero, pow_one,
        Nat.cast_zero, zero_mul, one_mul, zero_add]
    · change |degreeCurvature D₂ D₃ D₄ d N y| ≤
        45000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2)
      calc
        |degreeCurvature D₂ D₃ D₄ d N y| ≤
            12000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2) := hc
        _ ≤ 45000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2) := by
          exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg Gamma, hd.le]) hK.le
    · change |degreeRate D₂ D₃ D₄ d N y ^ 2 +
          dHat D₂ D₃ D₄ d N y * degreeCurvature D₂ D₃ D₄ d N y| ≤
        45000 * Gamma ^ 2 * d ^ 2 / (N ^ 2 * P ^ 2)
      calc
        _ ≤ |degreeRate D₂ D₃ D₄ d N y ^ 2| +
            |dHat D₂ D₃ D₄ d N y * degreeCurvature D₂ D₃ D₄ d N y| := abs_add_le _ _
        _ ≤ (104 * Gamma * d / (N * P)) ^ 2 +
            d * (12000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2)) := add_le_add hR2 hUC
        _ = 22816 * Gamma ^ 2 * d ^ 2 / (N ^ 2 * P ^ 2) := by
          rw [div_pow]
          have hNPsq : (N * P) ^ 2 = N ^ 2 * P ^ 2 := by ring
          rw [hNPsq]
          field_simp
          ring
        _ ≤ 45000 * Gamma ^ 2 * d ^ 2 / (N ^ 2 * P ^ 2) :=
          div_le_div_of_nonneg_right
            (by nlinarith [mul_nonneg (sq_nonneg Gamma) (sq_nonneg d)]) hK.le
    · change |2 * dHat D₂ D₃ D₄ d N y * degreeRate D₂ D₃ D₄ d N y ^ 2 +
          dHat D₂ D₃ D₄ d N y ^ 2 * degreeCurvature D₂ D₃ D₄ d N y| ≤
        45000 * Gamma ^ 2 * d ^ 3 / (N ^ 2 * P ^ 2)
      calc
        _ ≤ 2 * |dHat D₂ D₃ D₄ d N y * degreeRate D₂ D₃ D₄ d N y ^ 2| +
            |dHat D₂ D₃ D₄ d N y ^ 2 * degreeCurvature D₂ D₃ D₄ d N y| := by
          calc
            _ ≤ |2 * (dHat D₂ D₃ D₄ d N y * degreeRate D₂ D₃ D₄ d N y ^ 2)| +
                |dHat D₂ D₃ D₄ d N y ^ 2 * degreeCurvature D₂ D₃ D₄ d N y| := by
              simpa only [mul_assoc] using abs_add_le
                (2 * (dHat D₂ D₃ D₄ d N y * degreeRate D₂ D₃ D₄ d N y ^ 2))
                (dHat D₂ D₃ D₄ d N y ^ 2 * degreeCurvature D₂ D₃ D₄ d N y)
            _ = _ := by simp only [abs_mul]; norm_num
        _ ≤ 2 * (d * (104 * Gamma * d / (N * P)) ^ 2) +
            d ^ 2 * (12000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hUR2 (by norm_num)) hU2C
        _ = 33632 * Gamma ^ 2 * d ^ 3 / (N ^ 2 * P ^ 2) := by
          rw [div_pow]
          have hNPsq : (N * P) ^ 2 = N ^ 2 * P ^ 2 := by ring
          rw [hNPsq]
          field_simp
          ring
        _ ≤ 45000 * Gamma ^ 2 * d ^ 3 / (N ^ 2 * P ^ 2) :=
          div_le_div_of_nonneg_right
            (by nlinarith [mul_nonneg (sq_nonneg Gamma) (pow_nonneg hd.le 3)]) hK.le
    · change |3 * dHat D₂ D₃ D₄ d N y ^ 2 * degreeRate D₂ D₃ D₄ d N y ^ 2 +
          dHat D₂ D₃ D₄ d N y ^ 3 * degreeCurvature D₂ D₃ D₄ d N y| ≤
        45000 * Gamma ^ 2 * d ^ 4 / (N ^ 2 * P ^ 2)
      calc
        _ ≤ 3 * |dHat D₂ D₃ D₄ d N y ^ 2 * degreeRate D₂ D₃ D₄ d N y ^ 2| +
            d * |dHat D₂ D₃ D₄ d N y ^ 2 * degreeCurvature D₂ D₃ D₄ d N y| := by
          rw [show dHat D₂ D₃ D₄ d N y ^ 3 * degreeCurvature D₂ D₃ D₄ d N y =
            dHat D₂ D₃ D₄ d N y *
              (dHat D₂ D₃ D₄ d N y ^ 2 * degreeCurvature D₂ D₃ D₄ d N y) by ring]
          calc
            _ ≤ |3 * (dHat D₂ D₃ D₄ d N y ^ 2 * degreeRate D₂ D₃ D₄ d N y ^ 2)| +
                |dHat D₂ D₃ D₄ d N y *
                  (dHat D₂ D₃ D₄ d N y ^ 2 * degreeCurvature D₂ D₃ D₄ d N y)| := by
              simpa only [mul_assoc] using abs_add_le
                (3 * (dHat D₂ D₃ D₄ d N y ^ 2 * degreeRate D₂ D₃ D₄ d N y ^ 2))
                (dHat D₂ D₃ D₄ d N y *
                  (dHat D₂ D₃ D₄ d N y ^ 2 * degreeCurvature D₂ D₃ D₄ d N y))
            _ = 3 * |dHat D₂ D₃ D₄ d N y ^ 2 * degreeRate D₂ D₃ D₄ d N y ^ 2| +
                dHat D₂ D₃ D₄ d N y *
                  |dHat D₂ D₃ D₄ d N y ^ 2 * degreeCurvature D₂ D₃ D₄ d N y| := by
              simp only [abs_mul, abs_of_nonneg hu0]
              norm_num
            _ ≤ _ := add_le_add (le_refl _)
              (mul_le_mul_of_nonneg_right hu (abs_nonneg _))
        _ ≤ 3 * (d ^ 2 * (104 * Gamma * d / (N * P)) ^ 2) +
            d * (d ^ 2 * (12000 * Gamma ^ 2 * d / (N ^ 2 * P ^ 2))) :=
          add_le_add (mul_le_mul_of_nonneg_left hU2R2 (by norm_num))
            (mul_le_mul_of_nonneg_left hU2C hd.le)
        _ = 44448 * Gamma ^ 2 * d ^ 4 / (N ^ 2 * P ^ 2) := by
          rw [div_pow]
          have hNPsq : (N * P) ^ 2 = N ^ 2 * P ^ 2 := by ring
          rw [hNPsq]
          field_simp
          ring
        _ ≤ 45000 * Gamma ^ 2 * d ^ 4 / (N ^ 2 * P ^ 2) :=
          div_le_div_of_nonneg_right
            (by nlinarith [mul_nonneg (sq_nonneg Gamma) (pow_nonneg hd.le 4)]) hK.le
  have hchoose : (Nat.choose j s : ℝ) * (s : ℝ) ≤ 64 := by
    interval_cases j <;> interval_cases s <;> norm_num [Nat.choose]
  have hden : 0 < 4 * Gamma * d ^ j := by positivity
  have hpow : d ^ j = d ^ s * d ^ (j - s) := by
    rw [← pow_add]
    congr 1
    omega
  have hscale : d ^ s / d ^ j = testScale d j s := by
    unfold testScale
    rw [inv_pow, hpow]
    field_simp
  unfold correctionCurvature
  change |(Nat.choose j s : ℝ) * (s : ℝ) * num / (4 * Gamma * d ^ j)| ≤ _
  rw [abs_div, abs_of_pos hden, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (Nat.choose j s : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ (s : ℝ))]
  calc
    (Nat.choose j s : ℝ) * (s : ℝ) * |num| / (4 * Gamma * d ^ j) ≤
        64 * (45000 * Gamma ^ 2 * d ^ s / (N ^ 2 * P ^ 2)) /
          (4 * Gamma * d ^ j) :=
      div_le_div_of_nonneg_right
        (mul_le_mul hchoose hnum (abs_nonneg _) (by norm_num)) hden.le
    _ = 720000 * Gamma * (d ^ s / d ^ j) / (N ^ 2 * P ^ 2) := by
      field_simp
      ring
    _ = 720000 * Gamma * testScale d j s / (N ^ 2 * P ^ 2) := by rw [hscale]
    _ ≤ 1000000 * Gamma ^ 2 * testScale d j s / (N ^ 2 * P ^ 2) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by nlinarith [R.Gamma_one])
          (pow_nonneg (inv_nonneg.mpr hd.le) _)) hK.le

/-- The actual second derivative of `zeta`, bounded solely from the source
registry and the numeric large-parameter budget. -/
theorem zetaCurvature_bound_at_step
    {D₂ D₃ D₄ Gamma epsilon d N x P y : ℝ} {j s : ℕ}
    (R : DeltaStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (L : TestLargeDCondition Gamma epsilon d N P j s)
    (hy : y ∈ Icc x (x + 1)) (hsj : s ≤ j) (hj : j ≤ 4) :
    |zetaCurvature D₂ D₃ D₄ Gamma epsilon d N j s y| ≤
      d ^ ((s : ℝ) - j - epsilon) / N := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.degree.d_one
  have hGamma : 0 < Gamma := lt_of_lt_of_le (by norm_num) R.degree.Gamma_one
  have hpV := pV_pos R.degree.N_pos (R.degree.before_end y hy)
  have hpV1 := pV_le_one R.degree.N_pos (R.degree.time_nonneg y hy)
  have hpM0 := pM_nonneg hd R.degree.N_pos (R.degree.time_nonneg y hy)
  have hpM1 := pM_le_inv hd R.degree.N_pos (R.degree.before_end y hy).le
  have hNP : 0 < N * P := mul_pos R.degree.N_pos R.degree.P_pos
  have hNpV : 0 < N * pV N y := mul_pos R.degree.N_pos hpV
  have hNPle : N * P ≤ N * pV N y :=
    mul_le_mul_of_nonneg_left (R.degree.pV_floor y hy) R.degree.N_pos.le
  have hinside0 : 0 ≤ testInside D₂ D₃ D₄ Gamma d N j s y := by
    unfold testInside zHat
    have hq0 : 0 ≤ q D₂ D₃ D₄ d N y := (q_pos hpV).le
    have hdHat0 : 0 ≤ dHat D₂ D₃ D₄ d N y := (dHat_pos hd hpV).le
    positivity
  have hinside : testInside D₂ D₃ D₄ Gamma d N j s y ≤
      d ^ ((s : ℝ) - j + 9 * epsilon / 1600) :=
    (testInside_source_upper R.degree.d_one R.degree.Gamma_one hpV hpV1 hpM0 hpM1
      R.degree.D₂_nonneg R.degree.D₃_nonneg R.degree.D₄_nonneg hsj hj).trans L.inside_upper
  have hrate := testInsideRate_bound_at_step R.degree hy hsj hj
  have hzHat : |zHatCurvature D₂ D₃ D₄ d N j s y| ≤
      d ^ ((s : ℝ) - j - epsilon) / N :=
    zHatCurvature_largeD R.degree.d_one R.degree.N_pos R.degree.Gamma_one
      R.degree.P_pos (R.degree.pV_floor y hy) hpV1 hpM0 hpM1
      R.degree.D₂_nonneg R.degree.D₃_nonneg R.degree.D₄_nonneg
      R.degree.D₂_bound R.degree.D₃_bound R.degree.D₄_bound hsj hj
      L.zHat_second_order
  have hscale : testScale d j s = d ^ ((s : ℝ) - j) := inv_pow_eq_rpow_sub hd hsj
  have hcorr : |correctionCurvature D₂ D₃ D₄ Gamma d N j s y| ≤
      1000000 * Gamma ^ 2 * d ^ ((s : ℝ) - j) / (N ^ 2 * P ^ 2) := by
    simpa only [hscale] using correctionCurvature_bound_at_step R.degree hy hsj hj
  have htestCurv : |testInsideCurvature2 D₂ D₃ D₄ Gamma d N j s y| ≤
      d ^ ((s : ℝ) - j - epsilon) / N +
        1000000 * Gamma ^ 2 * d ^ ((s : ℝ) - j) / (N ^ 2 * P ^ 2) := by
    unfold testInsideCurvature2
    exact (abs_add_le _ _).trans (add_le_add hzHat hcorr)
  have hgamma0 : 0 ≤ gamma Gamma N y := by unfold gamma; positivity
  have hslope0 : 0 ≤ gammaSlope Gamma N y := by unfold gammaSlope; positivity
  have hgamma : |gamma Gamma N y| ≤ 76800 * Gamma / (N * P) := by
    rw [abs_of_nonneg hgamma0]
    unfold gamma
    rw [div_le_div_iff₀ hNpV hNP]
    exact mul_le_mul_of_nonneg_left hNPle (by positivity)
  have hdenP2 : 0 < N ^ 2 * P ^ 2 :=
    mul_pos (sq_pos_of_pos R.degree.N_pos) (sq_pos_of_pos R.degree.P_pos)
  have hdenV2 : 0 < N ^ 2 * pV N y ^ 2 :=
    mul_pos (sq_pos_of_pos R.degree.N_pos) (sq_pos_of_pos hpV)
  have hP2 : P ^ 2 ≤ pV N y ^ 2 := by
    nlinarith [mul_self_le_mul_self R.degree.P_pos.le (R.degree.pV_floor y hy)]
  have hslope : |gammaSlope Gamma N y| ≤ 614400 * Gamma / (N ^ 2 * P ^ 2) := by
    rw [abs_of_nonneg hslope0]
    unfold gammaSlope
    rw [div_le_div_iff₀ hdenV2 hdenP2]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hP2 (sq_nonneg N)) (by positivity)
  have hxi : |xi Gamma epsilon d N y| ≤ d ^ (-epsilon / 64) := by
    rw [abs_of_pos (xi_pos hd hpV)]
    exact R.xi_upper y hy
  have hin : |testInside D₂ D₃ D₄ Gamma d N j s y| ≤
      d ^ ((s : ℝ) - j + 9 * epsilon / 1600) := by
    rw [abs_of_nonneg hinside0]
    exact hinside
  have hX0 : 0 ≤ d ^ (-epsilon / 64) := Real.rpow_nonneg hd.le _
  have hU0 : 0 ≤ d ^ ((s : ℝ) - j + 9 * epsilon / 1600) := Real.rpow_nonneg hd.le _
  have hV0 : 0 ≤ 5000 * Gamma * d ^ ((s : ℝ) - j) / (N * P) := by positivity
  have hW0 : 0 ≤ d ^ ((s : ℝ) - j - epsilon) / N +
      1000000 * Gamma ^ 2 * d ^ ((s : ℝ) - j) / (N ^ 2 * P ^ 2) := by
    apply add_nonneg
    · exact div_nonneg (Real.rpow_nonneg hd.le _) R.degree.N_pos.le
    · exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Gamma))
          (Real.rpow_nonneg hd.le _)) hdenP2.le
  have hG0 : 0 ≤ 76800 * Gamma / (N * P) := by positivity
  have hH0 : 0 ≤ 614400 * Gamma / (N ^ 2 * P ^ 2) := by positivity
  rw [zetaCurvature_eq_formula hd R.degree.N_pos hGamma hpV hsj hj]
  apply (zetaCurvatureFormula_bound
    (X := d ^ (-epsilon / 64))
    (U := d ^ ((s : ℝ) - j + 9 * epsilon / 1600))
    (V := 5000 * Gamma * d ^ ((s : ℝ) - j) / (N * P))
    (W := d ^ ((s : ℝ) - j - epsilon) / N +
      1000000 * Gamma ^ 2 * d ^ ((s : ℝ) - j) / (N ^ 2 * P ^ 2))
    (G := 76800 * Gamma / (N * P))
    (H := 614400 * Gamma / (N ^ 2 * P ^ 2))
    hX0 hU0 hV0 hW0 hG0 hH0 hxi hin hrate htestCurv hgamma hslope).trans
  exact L.zeta_second_order

/-- Uniform constructor for a finite test registry from the source stopping
inequality and the purely numerical large-parameter registry.  In particular,
neither of the two curvature estimates is an input: both are derived from the
exact trajectory formulas above. -/
theorem TestStepRegistry.of_source
    {D₂ D₃ D₄ Gamma epsilon d N x P : ℝ} {j s : ℕ}
    (R : DeltaStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (L : TestLargeDCondition Gamma epsilon d N P j s)
    (hepsilon : 0 ≤ epsilon)
    (hstop : ∀ y ∈ Icc x (x + 1), d ^ (-epsilon ^ 3) ≤ pV N y)
    (hvertex : 7 * epsilon ^ 3 ≤ epsilon / 512)
    (hexp : d ^ (-epsilon / 512) ≤ exp (-3 * Gamma))
    (hsj : s ≤ j) (hj : j ≤ 4) :
    TestStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P j s := by
  refine ⟨R, hsj, hj, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.degree.d_one
    have hpV := pV_pos R.degree.N_pos (R.degree.before_end y hy)
    have hpM0 := pM_nonneg hd R.degree.N_pos (R.degree.time_nonneg y hy)
    have hpM1 := pM_le_inv hd R.degree.N_pos (R.degree.before_end y hy).le
    have hdHatStrong := dHat_source_lower_strong
      R.degree.d_one R.degree.Gamma_one hpV (hstop y hy) hpM0 hpM1
      R.degree.D₂_nonneg R.degree.D₃_nonneg R.degree.D₄_nonneg
      R.degree.D₂_bound R.degree.D₃_bound R.degree.D₄_bound hvertex hexp
    exact testInside_source_lower R.degree.d_one R.degree.Gamma_one hepsilon
      hpV hpM0 hsj hj hdHatStrong L.correction_denominator
  · intro y hy
    have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.degree.d_one
    have hpV := pV_pos R.degree.N_pos (R.degree.before_end y hy)
    have hpV1 := pV_le_one R.degree.N_pos (R.degree.time_nonneg y hy)
    have hpM0 := pM_nonneg hd R.degree.N_pos (R.degree.time_nonneg y hy)
    have hpM1 := pM_le_inv hd R.degree.N_pos (R.degree.before_end y hy).le
    exact (testInside_source_upper R.degree.d_one R.degree.Gamma_one hpV hpV1
      hpM0 hpM1 R.degree.D₂_nonneg R.degree.D₃_nonneg R.degree.D₄_nonneg
      hsj hj).trans L.inside_upper
  · intro y hy
    have hd : 0 < d := lt_of_lt_of_le (by norm_num) R.degree.d_one
    exact zHatCurvature_largeD R.degree.d_one R.degree.N_pos
      R.degree.Gamma_one R.degree.P_pos (R.degree.pV_floor y hy)
      (pV_le_one R.degree.N_pos (R.degree.time_nonneg y hy))
      (pM_nonneg hd R.degree.N_pos (R.degree.time_nonneg y hy))
      (pM_le_inv hd R.degree.N_pos (R.degree.before_end y hy).le)
      R.degree.D₂_nonneg R.degree.D₃_nonneg R.degree.D₄_nonneg
      R.degree.D₂_bound R.degree.D₃_bound R.degree.D₄_bound hsj hj
      L.zHat_second_order
  · intro y hy
    exact zetaCurvature_bound_at_step R L hy hsj hj

/-- End-to-end source constructor, starting with the elementary degree
registry.  The delta envelope and both finite-test curvatures are constructed
internally from the stopping and numeric large-parameter inequalities. -/
theorem TestStepRegistry.of_degree_source
    {D₂ D₃ D₄ Gamma epsilon d N x P : ℝ} {j s : ℕ}
    (R : DegreeStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P)
    (L : TestLargeDCondition Gamma epsilon d N P j s)
    (hepsilon : 0 ≤ epsilon)
    (hstop : ∀ y ∈ Icc x (x + 1), d ^ (-epsilon ^ 3) ≤ pV N y)
    (hamp : 9600 * Gamma * epsilon ^ 3 ≤ epsilon / 64)
    (hvertexDelta : 7 * epsilon ^ 3 ≤ epsilon / 64)
    (hexpDelta : d ^ (-epsilon / 64) ≤ exp (-3 * Gamma))
    (hlargeDelta : deltaLargeDCondition Gamma epsilon d N P)
    (hvertexTest : 7 * epsilon ^ 3 ≤ epsilon / 512)
    (hexpTest : d ^ (-epsilon / 512) ≤ exp (-3 * Gamma))
    (hsj : s ≤ j) (hj : j ≤ 4) :
    TestStepRegistry D₂ D₃ D₄ Gamma epsilon d N x P j s := by
  exact TestStepRegistry.of_source
    (DeltaStepRegistry.of_source R hepsilon hstop hamp hvertexDelta
      hexpDelta hlargeDelta)
    L hepsilon hstop hvertexTest hexpTest hsj hj

/-- Degree-trajectory one-step estimate once the explicit large-`d`
second-order bound has been verified.  The threshold `d ≥ 1` is the one
needed for the real powers in the target bound to be nonnegative. -/
theorem degree_oneStepTaylor_of_large_d {f f' : ℝ → ℝ} {x d epsilon N : ℝ}
    (hd : 1 ≤ d) (hN : 0 < N)
    (hf : ∀ y ∈ Icc x (x + 1), HasDerivAt f (f' y) y)
    (hvar : ∀ y ∈ Icc x (x + 1),
      |f' y - f' x| ≤ d ^ (1 - epsilon) / N) :
    |f (x + 1) - f x - f' x| ≤ d ^ (1 - epsilon) / N := by
  apply oneStepTaylorEstimate
  · positivity
  · exact hf
  · exact hvar

/-- Test-trajectory one-step estimate, with the source exponent
`d^(s-j-epsilon)/N`. -/
theorem test_oneStepTaylor_of_large_d {f f' : ℝ → ℝ}
    {x d epsilon N : ℝ} {j s : ℕ}
    (hd : 1 ≤ d) (hN : 0 < N)
    (hf : ∀ y ∈ Icc x (x + 1), HasDerivAt f (f' y) y)
    (hvar : ∀ y ∈ Icc x (x + 1),
      |f' y - f' x| ≤ d ^ ((s : ℝ) - j - epsilon) / N) :
    |f (x + 1) - f x - f' x| ≤ d ^ ((s : ℝ) - j - epsilon) / N := by
  apply oneStepTaylorEstimate
  · positivity
  · exact hf
  · exact hvar

end

end Erdos136.CFMTrajectories
