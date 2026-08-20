/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveVaughanAsymptotic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absorption of the two power-sieve Vaughan budgets

This file discharges the two explicit budget hypotheses left by
`PowerSieveVaughanAsymptotic`.  The proof keeps the sharp auxiliary core
throughout: replacing either cutoff by the global square-root cutoff would
destroy the required power saving.
-/

namespace Erdos48

open Filter
open scoped Topology
open BoundedGaps.Maynard

noncomputable section

theorem sqrt_powerSieveX_eq (n L : ℕ) :
    Real.sqrt (powerSieveX n L : ℝ) =
      (powerSieveVaughanCutoff n L : ℝ) := by
  have hsq : ((powerSieveVaughanCutoff n L : ℝ) ^ 2) =
      (powerSieveX n L : ℝ) := by
    exact_mod_cast powerSieveVaughanCutoff_sq n L
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  positivity

theorem vaughanCubeRoot_powerSieveX_eq (n L : ℕ) :
    vaughanCubeRoot (powerSieveX n L) = (n : ℝ) ^ (80 * L) := by
  unfold vaughanCubeRoot powerSieveX
  rw [Nat.cast_pow]
  calc
    ((n : ℝ) ^ (240 * L)) ^ (1 / 3 : ℝ) =
        (n : ℝ) ^ (((240 * L : ℕ) : ℝ) * (1 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul (Nat.cast_nonneg n) _ _).symm
    _ = (n : ℝ) ^ (80 * L : ℕ) := by
      rw [← Real.rpow_natCast]
      congr 1
      push_cast
      ring

theorem vaughanSixthRoot_powerSieveX_eq (n L : ℕ) :
    vaughanSixthRoot (powerSieveX n L) = (n : ℝ) ^ (40 * L) := by
  unfold vaughanSixthRoot powerSieveX
  rw [Nat.cast_pow]
  calc
    ((n : ℝ) ^ (240 * L)) ^ (1 / 6 : ℝ) =
        (n : ℝ) ^ (((240 * L : ℕ) : ℝ) * (1 / 6 : ℝ)) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul (Nat.cast_nonneg n) _ _).symm
    _ = (n : ℝ) ^ (40 * L : ℕ) := by
      rw [← Real.rpow_natCast]
      congr 1
      push_cast
      ring

theorem sqrt_powerSieveSmoothBound_eq
    {n L : ℕ} (hL : 1 ≤ L) :
    Real.sqrt (powerSieveSmoothBound n L : ℝ) =
      (n ^ (60 * L - 3) : ℕ) := by
  have hsquare : (n ^ (60 * L - 3)) ^ 2 =
      powerSieveSmoothBound n L := by
    unfold powerSieveSmoothBound
    rw [← pow_mul]
    congr 1
    omega
  have hsquareR : (((n ^ (60 * L - 3) : ℕ) : ℝ) ^ 2) =
      (powerSieveSmoothBound n L : ℝ) := by exact_mod_cast hsquare
  rw [← hsquareR, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  positivity

theorem powerSieveAuxCore_mul_pow_three_le_vaughanCutoff
    {n L Q : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    powerSieveAuxCore n L Q * n ^ 3 ≤
      powerSieveVaughanCutoff n L := by
  have hcore := powerSieveAuxCore_le_productBase hn hL hQ
  calc
    powerSieveAuxCore n L Q * n ^ 3 ≤
        powerSieveProductBase n L * n ^ 3 :=
      Nat.mul_le_mul_right _ hcore
    _ = n ^ (120 * L - 4) := by
      unfold powerSieveProductBase
      rw [← pow_add]
      congr 1
      omega
    _ ≤ n ^ (120 * L) := pow_le_pow_right' hn (by omega)
    _ = powerSieveVaughanCutoff n L := rfl

theorem pow_two_mul_sqrt_auxCore_mul_le_cubeRoot
    {n L Q : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    (n : ℝ) ^ 2 *
        Real.sqrt ((powerSieveAuxCore n L Q : ℝ) * (n : ℝ)) ≤
      vaughanCubeRoot (powerSieveX n L) := by
  have hupper : powerSieveAuxCore n L Q * n ≤
      powerSieveSmoothBound n L := by
    simpa only [powerSieveAuxUpper, powerSieveAuxScale] using
      powerSieveAuxUpper_le_smoothBound hn hL hQ
  have hsqrt :
      Real.sqrt ((powerSieveAuxCore n L Q : ℝ) * (n : ℝ)) ≤
        (n ^ (60 * L - 3) : ℕ) := by
    calc
      Real.sqrt ((powerSieveAuxCore n L Q : ℝ) * (n : ℝ)) ≤
          Real.sqrt (powerSieveSmoothBound n L : ℝ) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast hupper
      _ = (n ^ (60 * L - 3) : ℕ) := sqrt_powerSieveSmoothBound_eq hL
  rw [vaughanCubeRoot_powerSieveX_eq]
  calc
    (n : ℝ) ^ 2 *
        Real.sqrt ((powerSieveAuxCore n L Q : ℝ) * (n : ℝ)) ≤
      (n : ℝ) ^ 2 * (n ^ (60 * L - 3) : ℕ) := by gcongr
    _ = (n : ℝ) ^ (60 * L - 1) := by
      norm_cast
      rw [← pow_add]
      congr 1
      omega
    _ ≤ (n : ℝ) ^ (80 * L) := by
      exact_mod_cast pow_le_pow_right' hn (by omega)

theorem pow_two_le_sixthRoot_powerSieveX
    {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (n : ℝ) ^ 2 ≤ vaughanSixthRoot (powerSieveX n L) := by
  rw [vaughanSixthRoot_powerSieveX_eq]
  exact_mod_cast pow_le_pow_right' hn (by omega : 2 ≤ 40 * L)

/-- At the sharp auxiliary cutoff, Vaughan's four-term polynomial has one
full factor `auxCore/n` of saving relative to `x`. -/
theorem mul_vaughanPolynomial_auxUpper_le
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    (n : ℝ) *
        vaughanPrimitiveMeanEquationOneOnePolynomial
          (powerSieveX n L) (powerSieveAuxUpper n L Q) ≤
      17 * (powerSieveX n L : ℝ) *
        (powerSieveAuxCore n L Q : ℝ) := by
  let x : ℝ := powerSieveX n L
  let C : ℝ := powerSieveAuxCore n L Q
  let M : ℝ := powerSieveAuxUpper n L Q
  let S : ℝ := Real.sqrt (powerSieveX n L : ℝ)
  let R : ℝ := vaughanCubeRoot (powerSieveX n L)
  let H : ℝ := vaughanSixthRoot (powerSieveX n L)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact vaughanCubeRoot_nonneg _
  have hM : M = C * (n : ℝ) := by
    dsimp [M, C]
    norm_cast
  have hSsq : S ^ 2 = x := by
    dsimp [S, x]
    rw [Real.sq_sqrt]
    positivity
  have hRcube : R ^ 3 = x := by
    exact vaughanCubeRoot_cube (powerSieveX n L)
  have hSH : S * R * H = x := by
    dsimp [S, R, H, x]
    rw [← vaughanSixthRoot_cube, ← vaughanSixthRoot_sq]
    calc
      vaughanSixthRoot (powerSieveX n L) ^ 3 *
          vaughanSixthRoot (powerSieveX n L) ^ 2 *
            vaughanSixthRoot (powerSieveX n L) =
        vaughanSixthRoot (powerSieveX n L) ^ 6 := by ring
      _ = (powerSieveX n L : ℝ) :=
        vaughanSixthRoot_pow_six (powerSieveX n L)
  have hCn3 : C * (n : ℝ) ^ 3 ≤ S := by
    dsimp only [C, S]
    rw [sqrt_powerSieveX_eq]
    exact_mod_cast powerSieveAuxCore_mul_pow_three_le_vaughanCutoff
      (by omega : 1 ≤ n) hL hQ
  have hn2sqrt :
      (n : ℝ) ^ 2 * Real.sqrt (C * (n : ℝ)) ≤ R := by
    simpa only [C, R] using pow_two_mul_sqrt_auxCore_mul_le_cubeRoot
      (by omega : 1 ≤ n) hL hQ
  have hn2H : (n : ℝ) ^ 2 ≤ H := by
    simpa only [H] using pow_two_le_sixthRoot_powerSieveX
      (by omega : 1 ≤ n) hL
  have hterm1 : (n : ℝ) * (4 * x) ≤ 4 * x * C := by
    have hnC : (n : ℝ) ≤ C := by
      dsimp [C, powerSieveAuxCore, powerSieveAuxScale]
      exact_mod_cast le_max_right
        (powerSieveProductBase n L / Q) n
    calc
      (n : ℝ) * (4 * x) = (4 * x) * (n : ℝ) := by ring
      _ ≤ (4 * x) * C :=
        mul_le_mul_of_nonneg_left hnC (by dsimp [x]; positivity)
      _ = 4 * x * C := by ring
  have hterm2 : (n : ℝ) * (2 * S * M ^ 2) ≤ 2 * x * C := by
    rw [hM]
    calc
      (n : ℝ) * (2 * S * (C * (n : ℝ)) ^ 2) =
          2 * (C * (n : ℝ) ^ 3) * S * C := by ring
      _ ≤ 2 * S * S * C := by gcongr
      _ = 2 * x * C := by rw [← hSsq]; ring
  have hterm3 :
      (n : ℝ) * (6 * R ^ 2 * (M * Real.sqrt M)) ≤
        6 * x * C := by
    rw [hM]
    calc
      (n : ℝ) *
          (6 * R ^ 2 *
            (C * (n : ℝ) * Real.sqrt (C * (n : ℝ)))) =
        6 * R ^ 2 * C *
          ((n : ℝ) ^ 2 * Real.sqrt (C * (n : ℝ))) := by ring
      _ ≤ 6 * R ^ 2 * C * R := by gcongr
      _ = 6 * x * C := by rw [← hRcube]; ring
  have hterm4 :
      (n : ℝ) * (5 * (S * R) * M) ≤ 5 * x * C := by
    rw [hM]
    calc
      (n : ℝ) * (5 * (S * R) * (C * (n : ℝ))) =
          5 * S * R * C * (n : ℝ) ^ 2 := by ring
      _ ≤ 5 * S * R * C * H := by
        exact mul_le_mul_of_nonneg_left hn2H
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hS0) hR0) hC0)
      _ = 5 * x * C := by rw [← hSH]; ring
  unfold vaughanPrimitiveMeanEquationOneOnePolynomial
  change (n : ℝ) *
      (4 * x + 2 * S * M ^ 2 + 6 * R ^ 2 * (M * Real.sqrt M) +
        5 * (S * R) * M) ≤ 17 * x * C
  calc
    (n : ℝ) *
        (4 * x + 2 * S * M ^ 2 + 6 * R ^ 2 * (M * Real.sqrt M) +
          5 * (S * R) * M) =
      (n : ℝ) * (4 * x) + (n : ℝ) * (2 * S * M ^ 2) +
        (n : ℝ) * (6 * R ^ 2 * (M * Real.sqrt M)) +
          (n : ℝ) * (5 * (S * R) * M) := by ring
    _ ≤ 4 * x * C + 2 * x * C + 6 * x * C + 5 * x * C := by
      gcongr
    _ = 17 * x * C := by ring

theorem vaughanLogPower_le_pow_four {x : ℕ} (hx : 4 ≤ x) :
    vaughanPrimitiveMeanEquationOneOneLogPower x ≤
      Real.log (x : ℝ) ^ 4 := by
  have hlog : 1 ≤ Real.log (x : ℝ) := one_le_log_natCast hx
  have hsqrt : Real.sqrt (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hlog)
  unfold vaughanPrimitiveMeanEquationOneOneLogPower
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- Finite auxiliary-budget estimate before logarithmic absorption. -/
theorem mul_primitiveEndpointVaughanBudget_auxUpper_le
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    (n : ℝ) *
        primitiveEndpointVaughanBudget (powerSieveX n L)
          (powerSieveAuxUpper n L Q) ≤
      17 * vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        (powerSieveX n L : ℝ) *
        (powerSieveAuxCore n L Q : ℝ) *
          Real.log (powerSieveX n L : ℝ) ^ 4 := by
  have hx : 4 ≤ powerSieveX n L := by
    have hn1 : 1 ≤ n := by omega
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      _ ≤ n ^ (240 * L) := pow_le_pow_right' hn1 (by omega)
      _ = powerSieveX n L := rfl
  have hpoly := mul_vaughanPolynomial_auxUpper_le hn hL hQ
  have hlog := vaughanLogPower_le_pow_four hx
  have hK : 0 ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) :=
    vaughanPrimitiveMeanEquationOneOneConstant_nonneg _
  have hpoly0 : 0 ≤
      vaughanPrimitiveMeanEquationOneOnePolynomial
        (powerSieveX n L) (powerSieveAuxUpper n L Q) :=
    vaughanPrimitiveMeanEquationOneOnePolynomial_nonneg _ (by positivity)
  have hlogPower0 : 0 ≤
      vaughanPrimitiveMeanEquationOneOneLogPower (powerSieveX n L) :=
    vaughanPrimitiveMeanEquationOneOneLogPower_nonneg _
  unfold primitiveEndpointVaughanBudget
  calc
    (n : ℝ) *
        (vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
          vaughanPrimitiveMeanEquationOneOnePolynomial
            (powerSieveX n L) (powerSieveAuxUpper n L Q) *
              vaughanPrimitiveMeanEquationOneOneLogPower
                (powerSieveX n L)) =
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        ((n : ℝ) *
          vaughanPrimitiveMeanEquationOneOnePolynomial
            (powerSieveX n L) (powerSieveAuxUpper n L Q)) *
              vaughanPrimitiveMeanEquationOneOneLogPower
                (powerSieveX n L) := by ring
    _ ≤ vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        (17 * (powerSieveX n L : ℝ) *
          (powerSieveAuxCore n L Q : ℝ)) *
            vaughanPrimitiveMeanEquationOneOneLogPower
              (powerSieveX n L) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly hK) hlogPower0
    _ ≤ vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        (17 * (powerSieveX n L : ℝ) *
          (powerSieveAuxCore n L Q : ℝ)) *
            Real.log (powerSieveX n L : ℝ) ^ 4 := by gcongr
    _ = _ := by ring

theorem auxCore_le_two_mul_mul_partnerThreshold
    {n L Q D : ℕ} (hD : 0 < D) (hL : 0 < L)
    (hscale : 2 * (D * L) ≤ powerSieveAuxCore n L Q) :
    powerSieveAuxCore n L Q ≤
      2 * (D * L) * powerSieveVaughanPartnerThreshold n L Q D := by
  let d : ℕ := D * L
  let C : ℕ := powerSieveAuxCore n L Q
  have hd : 0 < d := Nat.mul_pos hD hL
  have hk : 1 ≤ C / d := by
    rw [Nat.one_le_iff_ne_zero]
    exact (Nat.div_pos (by omega) hd).ne'
  have hlt : C < d * (C / d + 1) := Nat.lt_mul_div_succ C hd
  have hnext : d * (C / d + 1) ≤ 2 * d * (C / d) := by
    nlinarith [Nat.mul_le_mul_left d hk]
  exact hlt.le.trans (by
    simpa only [C, d, powerSieveVaughanPartnerThreshold] using hnext)

/-- Every fixed multiple of `log(n)^4` is eventually absorbed by
`sqrt n`. -/
theorem eventually_const_mul_log_pow_four_le_sqrt (B : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      B * Real.log (n : ℝ) ^ 4 ≤ Real.sqrt (n : ℝ) := by
  let E : ℝ := |B| + 1
  have hE : 0 < E := by dsimp [E]; linarith [abs_nonneg B]
  have hlo := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := hlo.bound (show 0 < E⁻¹ by positivity)
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn1)
  have hrpow0 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hlogpow0 : 0 ≤ Real.log (n : ℝ) ^ 4 := by positivity
  have hb' : Real.log (n : ℝ) ^ 4 ≤ E⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ) := by
    simp only [Function.comp_apply] at hn
    change ‖Real.log (n : ℝ) ^ (4 : ℝ)‖ ≤
      E⁻¹ * ‖(n : ℝ) ^ (1 / 2 : ℝ)‖ at hn
    have hpowEq : Real.log (n : ℝ) ^ (4 : ℝ) =
        Real.log (n : ℝ) ^ (4 : ℕ) :=
      Real.rpow_natCast (Real.log (n : ℝ)) 4
    rw [hpowEq] at hn
    calc
      Real.log (n : ℝ) ^ (4 : ℕ) ≤
          ‖(Real.log (n : ℝ) ^ (4 : ℕ) : ℝ)‖ :=
        Real.le_norm_self (Real.log (n : ℝ) ^ (4 : ℕ))
      _ ≤ E⁻¹ * ‖(n : ℝ) ^ (1 / 2 : ℝ)‖ := hn
      _ = E⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.norm_of_nonneg hrpow0]
  rw [Real.sqrt_eq_rpow]
  calc
    B * Real.log (n : ℝ) ^ 4 ≤
        |B| * Real.log (n : ℝ) ^ 4 := by
      gcongr
      exact le_abs_self B
    _ ≤ |B| * (E⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ)) := by gcongr
    _ = (|B| / E) * (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [inv_eq_one_div]
      ring
    _ ≤ 1 * (n : ℝ) ^ (1 / 2 : ℝ) := by
      gcongr
      rw [div_le_one hE]
      dsimp [E]
      linarith
    _ = (n : ℝ) ^ (1 / 2 : ℝ) := one_mul _

/-- The auxiliary Vaughan budget is eventually absorbed by the natural
partner threshold, uniformly in the dyadic block parameter. -/
theorem eventually_powerSieve_auxVaughanBudget_absorbed
    (L D : ℕ) (hL : 1 ≤ L) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveAuxUpper n L Q) ≤
        (powerSieveVaughanPartnerThreshold n L Q D : ℝ) *
          (powerSieveX n L : ℝ) := by
  let K : ℝ :=
    vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4)
  let B : ℝ := 680 * K * ((240 * L : ℕ) : ℝ) ^ 4 * (D * L : ℕ)
  have habsorb := eventually_const_mul_log_pow_four_le_sqrt B
  filter_upwards [habsorb,
      eventually_ge_atTop (max 2 (2 * (D * L)))] with n hlog hnlarge
  intro Q hQ
  have hn : 2 ≤ n := (le_max_left _ _).trans hnlarge
  have hn1 : 1 ≤ n := by omega
  have hscale : 2 * (D * L) ≤ powerSieveAuxCore n L Q := by
    exact ((le_max_right 2 (2 * (D * L))).trans hnlarge).trans
      (by
        unfold powerSieveAuxCore powerSieveAuxScale
        exact le_max_right _ _)
  have hcore := auxCore_le_two_mul_mul_partnerThreshold
    hD (by omega : 0 < L) hscale
  have hfinite := mul_primitiveEndpointVaughanBudget_auxUpper_le
    hn hL hQ
  let x : ℝ := powerSieveX n L
  let C : ℝ := powerSieveAuxCore n L Q
  let A : ℝ := powerSieveVaughanPartnerThreshold n L Q D
  let V : ℝ := primitiveEndpointVaughanBudget
    (powerSieveX n L) (powerSieveAuxUpper n L Q)
  let s : ℝ := Real.sqrt (n : ℝ)
  have hC : C ≤ 2 * (D * L : ℕ) * A := by
    dsimp [C, A]
    push_cast
    exact_mod_cast hcore
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact vaughanPrimitiveMeanEquationOneOneConstant_nonneg _
  have hfinite' : (n : ℝ) * V ≤
      17 * K * x * C * Real.log x ^ 4 := by
    simpa only [K, x, C, V] using hfinite
  have hlogx : Real.log x = ((240 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
    dsimp [x, powerSieveX]
    rw [Nat.cast_pow, Real.log_pow]
  have hsSq : s * s = (n : ℝ) := by
    dsimp [s]
    rw [Real.mul_self_sqrt]
    positivity
  have hscaled :
      (n : ℝ) * (20 * s * V) ≤ (n : ℝ) * (A * x) := by
    calc
      (n : ℝ) * (20 * s * V) = 20 * s * ((n : ℝ) * V) := by ring
      _ ≤ 20 * s *
          (17 * K * x * C * Real.log x ^ 4) := by gcongr
      _ = 340 * K * s * x * C * Real.log x ^ 4 := by ring
      _ ≤ 340 * K * s * x *
          (2 * (D * L : ℕ) * A) * Real.log x ^ 4 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hC (by positivity)) (by positivity)
      _ = (B * Real.log (n : ℝ) ^ 4) * s * A * x := by
        rw [hlogx, mul_pow]
        dsimp [B]
        push_cast
        ring
      _ ≤ s * s * A * x := by gcongr
      _ = (n : ℝ) * (A * x) := by rw [hsSq]; ring
  have hnR : (0 : ℝ) < n := by positivity
  have hgoal := le_of_mul_le_mul_left hscaled hnR
  simpa only [s, V, A, x] using hgoal

/-! ## Product-cutoff polynomial -/

theorem pow_two_le_mul_auxCore
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    n ^ 2 ≤ Q * powerSieveAuxCore n L Q := by
  have hcoreN : n ≤ powerSieveAuxCore n L Q := by
    unfold powerSieveAuxCore powerSieveAuxScale
    exact le_max_right _ _
  by_cases hnQ : n ≤ Q
  · calc
      n ^ 2 = n * n := by ring
      _ ≤ Q * powerSieveAuxCore n L Q := Nat.mul_le_mul hnQ hcoreN
  · have hQn : Q < n := Nat.lt_of_not_ge hnQ
    have hn3P : n ^ 3 ≤ powerSieveProductBase n L := by
      unfold powerSieveProductBase
      exact pow_le_pow_right' (by omega : 1 ≤ n) (by omega)
    have hmul : n ^ 2 * Q ≤ powerSieveProductBase n L := by
      calc
        n ^ 2 * Q ≤ n ^ 2 * n := Nat.mul_le_mul_left _ hQn.le
        _ = n ^ 3 := by ring
        _ ≤ powerSieveProductBase n L := hn3P
    have hdiv : n ^ 2 ≤ powerSieveProductBase n L / Q := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < Q)]
      exact hmul
    have hcore : n ^ 2 ≤ powerSieveAuxCore n L Q := by
      unfold powerSieveAuxCore
      exact hdiv.trans (le_max_left _ _)
    exact hcore.trans (by
      simpa only [one_mul] using Nat.mul_le_mul_right
        (powerSieveAuxCore n L Q) hQ)

theorem mul_auxCore_le_two_mul_smoothBound_mul_n
    {n L Q : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hQ : 1 ≤ Q) (hQupper : Q ≤ powerSieveSmoothBound n L) :
    Q * powerSieveAuxCore n L Q ≤
      2 * powerSieveSmoothBound n L * n := by
  let P := powerSieveProductBase n L
  let U := powerSieveSmoothBound n L
  have hcore : powerSieveAuxCore n L Q ≤ P / Q + n := by
    unfold powerSieveAuxCore powerSieveAuxScale
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hdiv : Q * (P / Q) ≤ P := Nat.mul_div_le P Q
  have hPU : P ≤ U := by
    dsimp [P, U, powerSieveProductBase, powerSieveSmoothBound]
    exact pow_le_pow_right' hn (by omega)
  calc
    Q * powerSieveAuxCore n L Q ≤ Q * (P / Q + n) :=
      Nat.mul_le_mul_left Q hcore
    _ = Q * (P / Q) + Q * n := by ring
    _ ≤ P + U * n := Nat.add_le_add hdiv (Nat.mul_le_mul_right n hQupper)
    _ ≤ U + U * n := Nat.add_le_add_right hPU _
    _ ≤ U * n + U * n := by
      gcongr
      simpa only [mul_one] using Nat.mul_le_mul_left U hn
    _ = 2 * U * n := by ring

theorem productVaughanCutoff_le_six_mul_mul_auxCore_mul_n
    {n L Q : ℕ} (hn : 1 ≤ n) (hQ : 1 ≤ Q) :
    powerSieveProductVaughanCutoff n L Q ≤
      6 * (Q * powerSieveAuxCore n L Q) * n := by
  let P := powerSieveProductBase n L
  let C := powerSieveAuxCore n L Q
  have hC1 : 1 ≤ C := by
    dsimp [C, powerSieveAuxCore, powerSieveAuxScale]
    exact hn.trans (le_max_right _ _)
  have hdivC : P / Q ≤ C := by
    dsimp [C, powerSieveAuxCore]
    exact le_max_left _ _
  have hlt : P < Q * (P / Q + 1) :=
    Nat.lt_mul_div_succ P (by omega : 0 < Q)
  have hsum : P / Q + 1 ≤ 2 * C := by omega
  have hP : P ≤ 2 * (Q * C) := by
    calc
      P ≤ Q * (P / Q + 1) := hlt.le
      _ ≤ Q * (2 * C) := Nat.mul_le_mul_left Q hsum
      _ = 2 * (Q * C) := by ring
  have hQn : Q * n ≤ Q * C := by
    apply Nat.mul_le_mul_left
    dsimp [C, powerSieveAuxCore, powerSieveAuxScale]
    exact le_max_right _ _
  calc
    powerSieveProductVaughanCutoff n L Q = 2 * (P + Q * n) * n := rfl
    _ ≤ 2 * (2 * (Q * C) + Q * C) * n := by gcongr
    _ = 6 * (Q * C) * n := by ring

theorem sqrt_productVaughanCutoff_le
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hQupper : Q ≤ powerSieveSmoothBound n L) :
    Real.sqrt (powerSieveProductVaughanCutoff n L Q : ℝ) ≤
      4 * (n ^ (60 * L - 2) : ℕ) := by
  let B := Q * powerSieveAuxCore n L Q
  let U := powerSieveSmoothBound n L
  let T := n ^ (60 * L - 2)
  have hB : B ≤ 2 * U * n := by
    simpa only [B, U] using mul_auxCore_le_two_mul_smoothBound_mul_n
      (by omega : 1 ≤ n) hL hQ hQupper
  have hM : powerSieveProductVaughanCutoff n L Q ≤ 6 * B * n := by
    simpa only [B] using
      productVaughanCutoff_le_six_mul_mul_auxCore_mul_n
        (by omega : 1 ≤ n) hQ
  have hUT : U * n ^ 2 = T ^ 2 := by
    dsimp [U, T, powerSieveSmoothBound]
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hM16 : powerSieveProductVaughanCutoff n L Q ≤ (4 * T) ^ 2 := by
    calc
      powerSieveProductVaughanCutoff n L Q ≤ 6 * B * n := hM
      _ ≤ 6 * (2 * U * n) * n := by gcongr
      _ = 12 * (U * n ^ 2) := by ring
      _ = 12 * T ^ 2 := by rw [hUT]
      _ ≤ 16 * T ^ 2 := by gcongr <;> norm_num
      _ = (4 * T) ^ 2 := by ring
  calc
    Real.sqrt (powerSieveProductVaughanCutoff n L Q : ℝ) ≤
        Real.sqrt ((((4 * T : ℕ) : ℝ) ^ 2)) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hM16
    _ = |(((4 * T) : ℕ) : ℝ)| := Real.sqrt_sq_eq_abs _
    _ = 4 * (T : ℝ) := by
      rw [abs_of_nonneg (by positivity)]
      norm_cast

theorem mul_auxCore_mul_pow_four_le_two_vaughanCutoff
    {n L Q : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hQupper : Q ≤ powerSieveSmoothBound n L) :
    (Q * powerSieveAuxCore n L Q) * n ^ 4 ≤
      2 * powerSieveVaughanCutoff n L := by
  have hB := mul_auxCore_le_two_mul_smoothBound_mul_n
    hn hL hQ hQupper
  calc
    (Q * powerSieveAuxCore n L Q) * n ^ 4 ≤
        (2 * powerSieveSmoothBound n L * n) * n ^ 4 :=
      Nat.mul_le_mul_right _ hB
    _ = 2 * n ^ (120 * L - 1) := by
      unfold powerSieveSmoothBound
      calc
        2 * n ^ (120 * L - 6) * n * n ^ 4 =
            2 * (n ^ (120 * L - 6) * n ^ 5) := by ring
        _ = 2 * n ^ ((120 * L - 6) + 5) := by rw [pow_add]
        _ = 2 * n ^ (120 * L - 1) := by congr 2 <;> omega
    _ ≤ 2 * n ^ (120 * L) := by gcongr <;> omega
    _ = 2 * powerSieveVaughanCutoff n L := rfl

/-- At the block-dependent product cutoff, two powers of `n` are saved
relative to `x * (Q*auxCore)`. -/
theorem mul_sq_vaughanPolynomial_productCutoff_le
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hQupper : Q ≤ powerSieveSmoothBound n L) :
    (n : ℝ) ^ 2 *
        vaughanPrimitiveMeanEquationOneOnePolynomial
          (powerSieveX n L) (powerSieveProductVaughanCutoff n L Q) ≤
      322 * (powerSieveX n L : ℝ) *
        (Q * powerSieveAuxCore n L Q : ℕ) := by
  let x : ℝ := powerSieveX n L
  let B : ℝ := (Q * powerSieveAuxCore n L Q : ℕ)
  let M : ℝ := powerSieveProductVaughanCutoff n L Q
  let S : ℝ := Real.sqrt (powerSieveX n L : ℝ)
  let R : ℝ := vaughanCubeRoot (powerSieveX n L)
  let H : ℝ := vaughanSixthRoot (powerSieveX n L)
  let T : ℝ := (n ^ (60 * L - 2) : ℕ)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; exact vaughanCubeRoot_nonneg _
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hSsq : S ^ 2 = x := by
    dsimp [S, x]
    rw [Real.sq_sqrt]
    positivity
  have hRcube : R ^ 3 = x := vaughanCubeRoot_cube _
  have hSH : S * R * H = x := by
    dsimp [S, R, H, x]
    rw [← vaughanSixthRoot_cube, ← vaughanSixthRoot_sq]
    calc
      vaughanSixthRoot (powerSieveX n L) ^ 3 *
          vaughanSixthRoot (powerSieveX n L) ^ 2 *
            vaughanSixthRoot (powerSieveX n L) =
        vaughanSixthRoot (powerSieveX n L) ^ 6 := by ring
      _ = (powerSieveX n L : ℝ) := vaughanSixthRoot_pow_six _
  have hn2B : (n : ℝ) ^ 2 ≤ B := by
    dsimp only [B]
    exact_mod_cast pow_two_le_mul_auxCore hn hL hQ
  have hM : M ≤ 6 * B * (n : ℝ) := by
    dsimp only [M, B]
    exact_mod_cast
      productVaughanCutoff_le_six_mul_mul_auxCore_mul_n
        (n := n) (L := L) (Q := Q) (by omega : 1 ≤ n) hQ
  have hBn4 : B * (n : ℝ) ^ 4 ≤ 2 * S := by
    dsimp only [B, S]
    rw [sqrt_powerSieveX_eq]
    exact_mod_cast mul_auxCore_mul_pow_four_le_two_vaughanCutoff
      (by omega : 1 ≤ n) hL hQ hQupper
  have hsqrtM : Real.sqrt M ≤ 4 * T := by
    simpa only [M, T] using sqrt_productVaughanCutoff_le hn hL hQ hQupper
  have hn3T : (n : ℝ) ^ 3 * T ≤ R := by
    dsimp only [T, R]
    rw [vaughanCubeRoot_powerSieveX_eq]
    norm_cast
    rw [← pow_add]
    exact pow_le_pow_right' (by omega : 1 ≤ n) (by omega)
  have hn3H : (n : ℝ) ^ 3 ≤ H := by
    dsimp only [H]
    rw [vaughanSixthRoot_powerSieveX_eq]
    exact_mod_cast pow_le_pow_right' (by omega : 1 ≤ n) (by omega)
  have hterm1 : (n : ℝ) ^ 2 * (4 * x) ≤ 4 * x * B := by
    calc
      (n : ℝ) ^ 2 * (4 * x) = (4 * x) * (n : ℝ) ^ 2 := by ring
      _ ≤ (4 * x) * B := mul_le_mul_of_nonneg_left hn2B (by
        dsimp [x]
        positivity)
      _ = 4 * x * B := by ring
  have hterm2 :
      (n : ℝ) ^ 2 * (2 * S * M ^ 2) ≤ 144 * x * B := by
    have hMpow : M ^ 2 ≤ (6 * B * (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hM0 hM 2
    calc
      (n : ℝ) ^ 2 * (2 * S * M ^ 2) ≤
          (n : ℝ) ^ 2 * (2 * S * (6 * B * (n : ℝ)) ^ 2) := by
        gcongr
      _ = 72 * S * B * (B * (n : ℝ) ^ 4) := by ring
      _ ≤ 72 * S * B * (2 * S) := by
        exact mul_le_mul_of_nonneg_left hBn4 (by positivity)
      _ = 144 * x * B := by rw [← hSsq]; ring
  have hterm3 :
      (n : ℝ) ^ 2 * (6 * R ^ 2 * (M * Real.sqrt M)) ≤
        144 * x * B := by
    calc
      (n : ℝ) ^ 2 * (6 * R ^ 2 * (M * Real.sqrt M)) ≤
          (n : ℝ) ^ 2 *
            (6 * R ^ 2 * ((6 * B * (n : ℝ)) * (4 * T))) := by
        gcongr
      _ = 144 * R ^ 2 * B * ((n : ℝ) ^ 3 * T) := by ring
      _ ≤ 144 * R ^ 2 * B * R := by
        exact mul_le_mul_of_nonneg_left hn3T (by positivity)
      _ = 144 * x * B := by rw [← hRcube]; ring
  have hterm4 :
      (n : ℝ) ^ 2 * (5 * (S * R) * M) ≤ 30 * x * B := by
    calc
      (n : ℝ) ^ 2 * (5 * (S * R) * M) ≤
          (n : ℝ) ^ 2 * (5 * (S * R) * (6 * B * (n : ℝ))) := by
        gcongr
      _ = 30 * S * R * B * (n : ℝ) ^ 3 := by ring
      _ ≤ 30 * S * R * B * H := by
        exact mul_le_mul_of_nonneg_left hn3H (by positivity)
      _ = 30 * x * B := by rw [← hSH]; ring
  unfold vaughanPrimitiveMeanEquationOneOnePolynomial
  change (n : ℝ) ^ 2 *
      (4 * x + 2 * S * M ^ 2 + 6 * R ^ 2 * (M * Real.sqrt M) +
        5 * (S * R) * M) ≤ 322 * x * B
  calc
    (n : ℝ) ^ 2 *
        (4 * x + 2 * S * M ^ 2 + 6 * R ^ 2 * (M * Real.sqrt M) +
          5 * (S * R) * M) =
      (n : ℝ) ^ 2 * (4 * x) + (n : ℝ) ^ 2 * (2 * S * M ^ 2) +
        (n : ℝ) ^ 2 * (6 * R ^ 2 * (M * Real.sqrt M)) +
          (n : ℝ) ^ 2 * (5 * (S * R) * M) := by ring
    _ ≤ 4 * x * B + 144 * x * B + 144 * x * B + 30 * x * B := by
      gcongr
    _ = 322 * x * B := by ring

/-- Finite product-cutoff budget estimate.  The factor `n^2` is the
power saving supplied by the block-dependent cutoff. -/
theorem mul_sq_primitiveEndpointVaughanBudget_productCutoff_le
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hQupper : Q ≤ powerSieveSmoothBound n L) :
    (n : ℝ) ^ 2 *
        primitiveEndpointVaughanBudget (powerSieveX n L)
          (powerSieveProductVaughanCutoff n L Q) ≤
      322 *
        vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        (powerSieveX n L : ℝ) *
        (Q * powerSieveAuxCore n L Q : ℕ) *
          Real.log (powerSieveX n L : ℝ) ^ 4 := by
  have hx : 4 ≤ powerSieveX n L := by
    have hn1 : 1 ≤ n := by omega
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      _ ≤ n ^ (240 * L) := pow_le_pow_right' hn1 (by omega)
      _ = powerSieveX n L := rfl
  have hpoly := mul_sq_vaughanPolynomial_productCutoff_le
    hn hL hQ hQupper
  have hlog := vaughanLogPower_le_pow_four hx
  have hK : 0 ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) :=
    vaughanPrimitiveMeanEquationOneOneConstant_nonneg _
  have hpoly0 : 0 ≤
      vaughanPrimitiveMeanEquationOneOnePolynomial
        (powerSieveX n L) (powerSieveProductVaughanCutoff n L Q) :=
    vaughanPrimitiveMeanEquationOneOnePolynomial_nonneg _ (by positivity)
  have hlogPower0 : 0 ≤
      vaughanPrimitiveMeanEquationOneOneLogPower (powerSieveX n L) :=
    vaughanPrimitiveMeanEquationOneOneLogPower_nonneg _
  unfold primitiveEndpointVaughanBudget
  calc
    (n : ℝ) ^ 2 *
        (vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
          vaughanPrimitiveMeanEquationOneOnePolynomial
            (powerSieveX n L) (powerSieveProductVaughanCutoff n L Q) *
              vaughanPrimitiveMeanEquationOneOneLogPower
                (powerSieveX n L)) =
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        ((n : ℝ) ^ 2 *
          vaughanPrimitiveMeanEquationOneOnePolynomial
            (powerSieveX n L) (powerSieveProductVaughanCutoff n L Q)) *
              vaughanPrimitiveMeanEquationOneOneLogPower
                (powerSieveX n L) := by ring
    _ ≤ vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        (322 * (powerSieveX n L : ℝ) *
          (Q * powerSieveAuxCore n L Q : ℕ)) *
            vaughanPrimitiveMeanEquationOneOneLogPower
              (powerSieveX n L) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly hK) hlogPower0
    _ ≤ vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        (322 * (powerSieveX n L : ℝ) *
          (Q * powerSieveAuxCore n L Q : ℕ)) *
            Real.log (powerSieveX n L : ℝ) ^ 4 := by gcongr
    _ = _ := by ring

/-- The product-cutoff Vaughan budget is eventually absorbed by the root
cardinality term.  The natural block hypothesis says that the dyadic root
scale is at most `sqrt n` times the number of available roots. -/
theorem eventually_powerSieve_productVaughanBudget_absorbed
    (L D : ℕ) (hL : 1 ≤ L) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, ∀ Q rootCard : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      (Q : ℝ) ≤ Real.sqrt (n : ℝ) * (rootCard : ℝ) →
      40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveProductVaughanCutoff n L Q) ≤
        (rootCard : ℝ) *
          (powerSieveVaughanPartnerThreshold n L Q D : ℝ) *
            (powerSieveX n L : ℝ) := by
  let K : ℝ :=
    vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4)
  let B : ℝ := 25760 * K * ((240 * L : ℕ) : ℝ) ^ 4 * (D * L : ℕ)
  have habsorb := eventually_const_mul_log_pow_four_le_sqrt B
  filter_upwards [habsorb,
      eventually_ge_atTop (max 2 (2 * (D * L)))] with n hlog hnlarge
  intro Q rootCard hQ hQupper hrootCard
  have hn : 2 ≤ n := (le_max_left _ _).trans hnlarge
  have hscale : 2 * (D * L) ≤ powerSieveAuxCore n L Q := by
    exact ((le_max_right 2 (2 * (D * L))).trans hnlarge).trans
      (by
        unfold powerSieveAuxCore powerSieveAuxScale
        exact le_max_right _ _)
  have hcore := auxCore_le_two_mul_mul_partnerThreshold
    hD (by omega : 0 < L) hscale
  have hfinite :=
    mul_sq_primitiveEndpointVaughanBudget_productCutoff_le
      hn hL hQ hQupper
  let x : ℝ := powerSieveX n L
  let C : ℝ := powerSieveAuxCore n L Q
  let A : ℝ := powerSieveVaughanPartnerThreshold n L Q D
  let V : ℝ := primitiveEndpointVaughanBudget
    (powerSieveX n L) (powerSieveProductVaughanCutoff n L Q)
  let s : ℝ := Real.sqrt (n : ℝ)
  let q : ℝ := rootCard
  have hC : C ≤ 2 * (D * L : ℕ) * A := by
    dsimp [C, A]
    push_cast
    exact_mod_cast hcore
  have hfinite' : (n : ℝ) ^ 2 * V ≤
      322 * K * x * ((Q : ℝ) * C) * Real.log x ^ 4 := by
    simpa only [K, x, C, V, Nat.cast_mul] using hfinite
  have hrootCard' : (Q : ℝ) ≤ s * q := by
    simpa only [s, q] using hrootCard
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact vaughanPrimitiveMeanEquationOneOneConstant_nonneg _
  have hlogx : Real.log x = ((240 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
    dsimp [x, powerSieveX]
    rw [Nat.cast_pow, Real.log_pow]
  have hsSq : s * s = (n : ℝ) := by
    dsimp [s]
    rw [Real.mul_self_sqrt]
    positivity
  have hlogN : B * Real.log (n : ℝ) ^ 4 ≤ (n : ℝ) :=
    hlog.trans (Real.sqrt_le_self_iff.mpr
      (Or.inr (by exact_mod_cast (show 1 ≤ n by omega))))
  have hscaled :
      (n : ℝ) ^ 2 * (40 * s * V) ≤
        (n : ℝ) ^ 2 * (q * A * x) := by
    calc
      (n : ℝ) ^ 2 * (40 * s * V) =
          40 * s * ((n : ℝ) ^ 2 * V) := by ring
      _ ≤ 40 * s *
          (322 * K * x * ((Q : ℝ) * C) * Real.log x ^ 4) := by
        gcongr
      _ = 12880 * K * s * x * (Q : ℝ) * C * Real.log x ^ 4 := by
        ring
      _ ≤ 12880 * K * s * x * (s * q) * C * Real.log x ^ 4 := by
        gcongr
      _ ≤ 12880 * K * s * x * (s * q) *
          (2 * (D * L : ℕ) * A) * Real.log x ^ 4 := by
        gcongr
      _ = (B * Real.log (n : ℝ) ^ 4) * (n : ℝ) * (q * A * x) := by
        rw [hlogx, mul_pow, ← hsSq]
        dsimp [B]
        push_cast
        ring
      _ ≤ (n : ℝ) * (n : ℝ) * (q * A * x) := by gcongr
      _ = (n : ℝ) ^ 2 * (q * A * x) := by ring
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hgoal := le_of_mul_le_mul_left hscaled hnSq
  simpa only [s, V, q, A, x] using hgoal

/-- Simultaneous form of the two eventual budget estimates, matching the
two hypotheses of `powerSieve_badRoots_card_mul_sqrt_le_card`. -/
theorem eventually_powerSieve_twoVaughanBudgets_absorbed
    (L D : ℕ) (hL : 1 ≤ L) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, ∀ Q rootCard : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      (Q : ℝ) ≤ Real.sqrt (n : ℝ) * (rootCard : ℝ) →
      (20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveAuxUpper n L Q) ≤
        (powerSieveVaughanPartnerThreshold n L Q D : ℝ) *
          (powerSieveX n L : ℝ)) ∧
      (40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveProductVaughanCutoff n L Q) ≤
        (rootCard : ℝ) *
          (powerSieveVaughanPartnerThreshold n L Q D : ℝ) *
            (powerSieveX n L : ℝ)) := by
  have haux := eventually_powerSieve_auxVaughanBudget_absorbed L D hL hD
  have hprod := eventually_powerSieve_productVaughanBudget_absorbed L D hL hD
  filter_upwards [haux, hprod] with n hauxN hprodN
  intro Q rootCard hQ hQupper hrootCard
  exact ⟨hauxN Q hQ, hprodN Q rootCard hQ hQupper hrootCard⟩

end


end Erdos48
