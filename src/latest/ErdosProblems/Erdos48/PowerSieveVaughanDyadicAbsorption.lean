/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveVaughanBudgetAbsorption
import ErdosProblems.Erdos48.PowerSieveDyadicBadRoots
import ErdosProblems.Erdos48.External.Erdos822.PrimeIntervals

/-!
# Vaughan-budget-free dyadic power-sieve bounds

This file transfers the asymptotic Vaughan budget estimates to the exact
cutoffs and partner threshold used by the dyadic bad-root theorem.  It then
packages the finite dyadic cardinality theorem without explicit Vaughan
budget assumptions.
-/

namespace Erdos48

open Filter
open scoped BigOperators Topology
open BoundedGaps.Maynard

noncomputable section

theorem primitiveEndpointVaughanBudget_mono_cutoff
    {x M N : ℕ} (hMN : M ≤ N) :
    primitiveEndpointVaughanBudget x M ≤
      primitiveEndpointVaughanBudget x N := by
  have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hpoly := vaughanPrimitiveMeanEquationOneOnePolynomial_mono x
    (q := (M : ℝ)) (r := (N : ℝ))
    (show (0 : ℝ) ≤ M by positivity) hMN'
  have hK : 0 ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) :=
    vaughanPrimitiveMeanEquationOneOneConstant_nonneg _
  have hlog : 0 ≤ vaughanPrimitiveMeanEquationOneOneLogPower x :=
    vaughanPrimitiveMeanEquationOneOneLogPower_nonneg _
  unfold primitiveEndpointVaughanBudget
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpoly hK) hlog

/-- The exact dyadic product-conductor cutoff is bounded by the slightly
larger cutoff used in the uniform product-budget estimate. -/
theorem powerSieveDyadicProductCutoff_le_productVaughanCutoff
    {n L Q : ℕ} :
    powerSieveDyadicProductCutoff n L Q ≤
      powerSieveProductVaughanCutoff n L Q := by
  let P := powerSieveProductBase n L
  let C := powerSieveAuxCore n L Q
  have hC : C ≤ P / Q + n := by
    dsimp [C, powerSieveAuxCore, powerSieveAuxScale]
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hQC : Q * C ≤ P + Q * n := by
    calc
      Q * C ≤ Q * (P / Q + n) := Nat.mul_le_mul_left Q hC
      _ = Q * (P / Q) + Q * n := by ring
      _ ≤ P + Q * n := Nat.add_le_add_right (Nat.mul_div_le P Q) _
  dsimp only [powerSieveDyadicProductCutoff, powerSieveAuxUpper,
    powerSieveAuxScale, powerSieveProductVaughanCutoff, C, P]
  calc
    2 * Q * (powerSieveAuxCore n L Q * n) =
        2 * (Q * powerSieveAuxCore n L Q) * n := by ring
    _ ≤ 2 * (powerSieveProductBase n L + Q * n) * n := by gcongr

/-- The reciprocal-mass partner threshold used by the dyadic theorem is
at least the uniform threshold with dilution constant `1000`. -/
theorem powerSieveVaughanPartnerThreshold_le_dyadicPartnerLower
    {n L Q : ℕ} (hL : 1 ≤ L) :
    powerSieveVaughanPartnerThreshold n L Q 1000 ≤
      powerSieveDyadicPartnerLower n L Q := by
  let C := powerSieveAuxCore n L Q
  let d := 1000 * L
  have hd : 0 < d := by dsimp [d]; positivity
  have hmul : (C / d) * (2 * d) ≤ 2 * C + 1 := by
    calc
      (C / d) * (2 * d) = 2 * ((C / d) * d) := by ring
      _ ≤ 2 * C := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self C d)
      _ ≤ 2 * C + 1 := by omega
  dsimp only [powerSieveVaughanPartnerThreshold,
    powerSieveDyadicPartnerLower, powerSieveAuxLower, C, d]
  rw [show 2000 * L = 2 * (1000 * L) by ring]
  rw [Nat.le_div_iff_mul_le (by positivity : 0 < 2 * (1000 * L))]
  simpa only [C, d] using hmul

/-- Uniform root density in every relevant dyadic block.  Large blocks use
the prime number theorem lower bound for `(Q,2Q]`; the finitely many smaller
blocks use Bertrand together with the eventual growth of `sqrt n`. -/
theorem eventually_powerSieve_dyadicPrimeBlock_rootDensity
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      (Q : ℝ) ≤ Real.sqrt (n : ℝ) *
        ((powerSieveDyadicPrimeBlock Q).card : ℝ) := by
  rcases Filter.eventually_atTop.1
      Erdos822.eventually_card_filter_Ioc_prime_half_interval_lower with
    ⟨T, hT⟩
  let C : ℝ := 600 * (L : ℝ)
  have habsorb := eventually_const_mul_log_pow_four_le_sqrt C
  filter_upwards [habsorb,
      eventually_ge_atTop (max 4 (T ^ 2))] with n habsorb hnlarge
  intro Q hQ hQupper
  have hn : 4 ≤ n := (le_max_left _ _).trans hnlarge
  have hn1 : 1 ≤ n := by omega
  have hsqrtT : (T : ℝ) ≤ Real.sqrt (n : ℝ) := by
    calc
      (T : ℝ) = Real.sqrt ((T : ℝ) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
        positivity
      _ ≤ Real.sqrt (n : ℝ) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast ((le_max_right 4 (T ^ 2)).trans hnlarge)
  by_cases hlargeQ : T ≤ Q
  · have hTtwoQ : T ≤ 2 * Q := hlargeQ.trans (by omega)
    have hpnt0 := hT (2 * Q) hTtwoQ
    have hpnt :
        ((2 * Q : ℕ) : ℝ) /
            (10 * Real.log ((2 * Q : ℕ) : ℝ)) ≤
          ((powerSieveDyadicPrimeBlock Q).card : ℝ) := by
      simpa only [show (2 * Q) / 2 = Q by omega,
        powerSieveDyadicPrimeBlock] using hpnt0
    have htwoQ : 2 * Q ≤ n ^ (120 * L - 5) := by
      calc
        2 * Q ≤ n * Q := Nat.mul_le_mul_right Q (by omega)
        _ ≤ n * powerSieveSmoothBound n L :=
          Nat.mul_le_mul_left n hQupper
        _ = n ^ (120 * L - 5) := by
          unfold powerSieveSmoothBound
          rw [← pow_succ']
          congr 1
          omega
    have hlogTwoQ :
        Real.log ((2 * Q : ℕ) : ℝ) ≤
          ((120 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
      have hlogBound := Real.log_le_log
        (show (0 : ℝ) < ((2 * Q : ℕ) : ℝ) by positivity)
        (show ((2 * Q : ℕ) : ℝ) ≤
            ((n ^ (120 * L - 5) : ℕ) : ℝ) by exact_mod_cast htwoQ)
      rw [Nat.cast_pow, Real.log_pow] at hlogBound
      exact hlogBound.trans (by
        gcongr
        exact_mod_cast (Nat.sub_le (120 * L) 5))
    have hlogOne : 1 ≤ Real.log (n : ℝ) := one_le_log_natCast hn
    have hlogLeFourth : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 4 := by
      calc
        Real.log (n : ℝ) = Real.log (n : ℝ) * 1 := by ring
        _ ≤ Real.log (n : ℝ) * Real.log (n : ℝ) ^ 3 := by
          gcongr
          exact one_le_pow₀ hlogOne
        _ = Real.log (n : ℝ) ^ 4 := by ring
    have hsqrtLog :
        5 * Real.log ((2 * Q : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
      calc
        5 * Real.log ((2 * Q : ℕ) : ℝ) ≤
            5 * (((120 * L : ℕ) : ℝ) * Real.log (n : ℝ)) := by
          gcongr
        _ = C * Real.log (n : ℝ) := by
          dsimp [C]
          push_cast
          ring
        _ ≤ C * Real.log (n : ℝ) ^ 4 := by
          dsimp [C]
          gcongr
        _ ≤ Real.sqrt (n : ℝ) := habsorb
    have hlogTwoQPos : 0 < Real.log ((2 * Q : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < 2 * Q by omega))
    have hmul := mul_le_mul hsqrtLog hpnt
      (show 0 ≤ ((2 * Q : ℕ) : ℝ) /
          (10 * Real.log ((2 * Q : ℕ) : ℝ)) by positivity)
      (Real.sqrt_nonneg _)
    calc
      (Q : ℝ) =
          (5 * Real.log ((2 * Q : ℕ) : ℝ)) *
            (((2 * Q : ℕ) : ℝ) /
              (10 * Real.log ((2 * Q : ℕ) : ℝ))) := by
        field_simp [hlogTwoQPos.ne']
        push_cast
        ring
      _ ≤ Real.sqrt (n : ℝ) *
          ((powerSieveDyadicPrimeBlock Q).card : ℝ) := hmul
  · obtain ⟨p, hpPrime, hQp, hpTwoQ⟩ := Nat.bertrand Q (by omega)
    have hpMem : p ∈ powerSieveDyadicPrimeBlock Q :=
      mem_powerSieveDyadicPrimeBlock.mpr ⟨hQp, hpTwoQ, hpPrime⟩
    have hcard : 1 ≤ (powerSieveDyadicPrimeBlock Q).card :=
      Finset.one_le_card.mpr ⟨p, hpMem⟩
    have hQsqrt : (Q : ℝ) ≤ Real.sqrt (n : ℝ) := by
      exact (show (Q : ℝ) ≤ T by exact_mod_cast (Nat.le_of_lt
        (Nat.lt_of_not_ge hlargeQ))).trans hsqrtT
    calc
      (Q : ℝ) ≤ Real.sqrt (n : ℝ) := hQsqrt
      _ = Real.sqrt (n : ℝ) * 1 := by ring
      _ ≤ Real.sqrt (n : ℝ) *
          ((powerSieveDyadicPrimeBlock Q).card : ℝ) := by
        gcongr
        exact_mod_cast hcard

/-! ## Direct root-endpoint budget -/

/-- At a block which can contain roots above the Page range (`n < 2Q`),
the Vaughan polynomial at the direct root cutoff has a full factor `1/n`
of saving relative to `xQ`. -/
theorem mul_vaughanPolynomial_two_mul_blockBase_le
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hQupper : Q ≤ powerSieveSmoothBound n L) (hlarge : n < 2 * Q) :
    (n : ℝ) *
        vaughanPrimitiveMeanEquationOneOnePolynomial
          (powerSieveX n L) (2 * Q) ≤
      50 * (powerSieveX n L : ℝ) * (Q : ℝ) := by
  let x : ℝ := powerSieveX n L
  let S : ℝ := Real.sqrt (powerSieveX n L : ℝ)
  let R : ℝ := vaughanCubeRoot (powerSieveX n L)
  let H : ℝ := vaughanSixthRoot (powerSieveX n L)
  let M : ℝ := (2 * Q : ℕ)
  let T : ℝ := (n ^ (60 * L - 3) : ℕ)
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; exact vaughanCubeRoot_nonneg _
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
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
  have hnQ : (n : ℝ) ≤ 2 * (Q : ℝ) := by exact_mod_cast hlarge.le
  have hnQleS : (n : ℝ) * (Q : ℝ) ≤ S := by
    dsimp only [S]
    rw [sqrt_powerSieveX_eq]
    exact_mod_cast (show n * Q ≤ powerSieveVaughanCutoff n L by
      calc
        n * Q ≤ n * powerSieveSmoothBound n L :=
          Nat.mul_le_mul_left n hQupper
        _ = n ^ (120 * L - 5) := by
          unfold powerSieveSmoothBound
          rw [← pow_succ']
          congr 1
          omega
        _ ≤ n ^ (120 * L) :=
          pow_le_pow_right' (by omega : 1 ≤ n) (by omega)
        _ = powerSieveVaughanCutoff n L := rfl)
  have hsqrtM : Real.sqrt M ≤ 2 * T := by
    have hnat : 2 * Q ≤ 4 * powerSieveSmoothBound n L := by
      calc
        2 * Q ≤ 2 * powerSieveSmoothBound n L :=
          Nat.mul_le_mul_left 2 hQupper
        _ ≤ 4 * powerSieveSmoothBound n L := by gcongr <;> omega
    calc
      Real.sqrt M ≤ Real.sqrt (4 * powerSieveSmoothBound n L : ℕ) := by
        apply Real.sqrt_le_sqrt
        dsimp only [M]
        exact_mod_cast hnat
      _ = Real.sqrt (4 : ℝ) *
          Real.sqrt (powerSieveSmoothBound n L : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num)]
      _ = 2 * T := by
        rw [sqrt_powerSieveSmoothBound_eq hL]
        dsimp only [T]
        norm_num
  have hnSqrtM : (n : ℝ) * Real.sqrt M ≤ 2 * R := by
    calc
      (n : ℝ) * Real.sqrt M ≤ (n : ℝ) * (2 * T) := by gcongr
      _ ≤ 2 * R := by
        dsimp only [T, R]
        rw [vaughanCubeRoot_powerSieveX_eq]
        norm_cast
        calc
          n * (2 * n ^ (60 * L - 3)) =
              2 * n ^ (60 * L - 2) := by
            rw [show n * (2 * n ^ (60 * L - 3)) =
              2 * (n * n ^ (60 * L - 3)) by ring, ← pow_succ']
            congr 2
            congr 1
            omega
          _ ≤ 2 * n ^ (80 * L) := by
            exact Nat.mul_le_mul_left 2
              (pow_le_pow_right' (by omega : 1 ≤ n) (by omega))
  have hnH : (n : ℝ) ≤ H := by
    dsimp only [H]
    rw [vaughanSixthRoot_powerSieveX_eq]
    norm_cast
    simpa only [pow_one] using
      pow_le_pow_right' (by omega : 1 ≤ n) (by omega : 1 ≤ 40 * L)
  have hM : M = 2 * (Q : ℝ) := by dsimp [M]; norm_num
  have hterm1 : (n : ℝ) * (4 * x) ≤ 8 * x * (Q : ℝ) := by
    calc
      (n : ℝ) * (4 * x) = 4 * x * (n : ℝ) := by ring
      _ ≤ 4 * x * (2 * (Q : ℝ)) := by gcongr
      _ = 8 * x * (Q : ℝ) := by ring
  have hterm2 :
      (n : ℝ) * (2 * S * M ^ 2) ≤ 8 * x * (Q : ℝ) := by
    rw [hM]
    calc
      (n : ℝ) * (2 * S * (2 * (Q : ℝ)) ^ 2) =
          8 * S * (Q : ℝ) * ((n : ℝ) * (Q : ℝ)) := by ring
      _ ≤ 8 * S * (Q : ℝ) * S := by gcongr
      _ = 8 * x * (Q : ℝ) := by rw [← hSsq]; ring
  have hterm3 :
      (n : ℝ) * (6 * R ^ 2 * (M * Real.sqrt M)) ≤
        24 * x * (Q : ℝ) := by
    calc
      (n : ℝ) * (6 * R ^ 2 * (M * Real.sqrt M)) =
        12 * R ^ 2 * (Q : ℝ) *
          ((n : ℝ) * Real.sqrt M) := by rw [hM]; ring
      _ ≤ 12 * R ^ 2 * (Q : ℝ) * (2 * R) := by gcongr
      _ = 24 * x * (Q : ℝ) := by rw [← hRcube]; ring
  have hterm4 :
      (n : ℝ) * (5 * (S * R) * M) ≤
        10 * x * (Q : ℝ) := by
    rw [hM]
    calc
      (n : ℝ) * (5 * (S * R) * (2 * (Q : ℝ))) =
          10 * S * R * (Q : ℝ) * (n : ℝ) := by ring
      _ ≤ 10 * S * R * (Q : ℝ) * H := by gcongr
      _ = 10 * x * (Q : ℝ) := by rw [← hSH]; ring
  unfold vaughanPrimitiveMeanEquationOneOnePolynomial
  rw [← hM]
  change (n : ℝ) *
      (4 * x + 2 * S * M ^ 2 + 6 * R ^ 2 * (M * Real.sqrt M) +
        5 * (S * R) * M) ≤ 50 * x * (Q : ℝ)
  calc
    (n : ℝ) *
        (4 * x + 2 * S * M ^ 2 + 6 * R ^ 2 * (M * Real.sqrt M) +
          5 * (S * R) * M) =
      (n : ℝ) * (4 * x) + (n : ℝ) * (2 * S * M ^ 2) +
        (n : ℝ) * (6 * R ^ 2 * (M * Real.sqrt M)) +
          (n : ℝ) * (5 * (S * R) * M) := by ring
    _ ≤ 8 * x * (Q : ℝ) + 8 * x * (Q : ℝ) +
        24 * x * (Q : ℝ) + 10 * x * (Q : ℝ) := by gcongr
    _ = 50 * x * (Q : ℝ) := by ring

theorem mul_primitiveEndpointVaughanBudget_two_mul_blockBase_le
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hQupper : Q ≤ powerSieveSmoothBound n L) (hlarge : n < 2 * Q) :
    (n : ℝ) *
        primitiveEndpointVaughanBudget (powerSieveX n L) (2 * Q) ≤
      50 *
        vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        (powerSieveX n L : ℝ) * (Q : ℝ) *
          Real.log (powerSieveX n L : ℝ) ^ 4 := by
  have hx : 4 ≤ powerSieveX n L := by
    have hn1 : 1 ≤ n := by omega
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      _ ≤ n ^ (240 * L) := pow_le_pow_right' hn1 (by omega)
      _ = powerSieveX n L := rfl
  have hpoly := mul_vaughanPolynomial_two_mul_blockBase_le
    hn hL hQupper hlarge
  have hpoly' : (n : ℝ) *
      vaughanPrimitiveMeanEquationOneOnePolynomial
        (powerSieveX n L) ((2 * Q : ℕ) : ℝ) ≤
      50 * (powerSieveX n L : ℝ) * (Q : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpoly
  have hlog := vaughanLogPower_le_pow_four hx
  have hK : 0 ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) :=
    vaughanPrimitiveMeanEquationOneOneConstant_nonneg _
  have hlogPower0 : 0 ≤
      vaughanPrimitiveMeanEquationOneOneLogPower (powerSieveX n L) :=
    vaughanPrimitiveMeanEquationOneOneLogPower_nonneg _
  unfold primitiveEndpointVaughanBudget
  calc
    (n : ℝ) *
        (vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
          vaughanPrimitiveMeanEquationOneOnePolynomial
            (powerSieveX n L) ((2 * Q : ℕ) : ℝ) *
              vaughanPrimitiveMeanEquationOneOneLogPower
                (powerSieveX n L)) =
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        ((n : ℝ) * vaughanPrimitiveMeanEquationOneOnePolynomial
          (powerSieveX n L) ((2 * Q : ℕ) : ℝ)) *
            vaughanPrimitiveMeanEquationOneOneLogPower
              (powerSieveX n L) := by ring
    _ ≤ vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        (50 * (powerSieveX n L : ℝ) * (Q : ℝ)) *
          vaughanPrimitiveMeanEquationOneOneLogPower
            (powerSieveX n L) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly' hK) hlogPower0
    _ ≤ vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        (50 * (powerSieveX n L : ℝ) * (Q : ℝ)) *
          Real.log (powerSieveX n L : ℝ) ^ 4 := by gcongr
    _ = 50 *
        vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        (powerSieveX n L : ℝ) * (Q : ℝ) *
          Real.log (powerSieveX n L : ℝ) ^ 4 := by ring

/-- The direct root-endpoint Vaughan budget used after the Page split.
The condition `n < 2Q` is essential: without it the assertion is false for
fixed tiny `Q`, because the Vaughan polynomial contains the term `4x`. -/
theorem eventually_powerSieve_rootVaughanBudget_absorbed
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L → n < 2 * Q →
      10 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L) (2 * Q) ≤
        (Q : ℝ) * (powerSieveX n L : ℝ) := by
  let K : ℝ :=
    vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4)
  let B : ℝ := 500 * K * ((240 * L : ℕ) : ℝ) ^ 4
  have habsorb := eventually_const_mul_log_pow_four_le_sqrt B
  filter_upwards [habsorb, eventually_ge_atTop 2] with n hlog hn
  intro Q hQ hQupper hlarge
  have hfinite :=
    mul_primitiveEndpointVaughanBudget_two_mul_blockBase_le
      hn hL hQupper hlarge
  let x : ℝ := powerSieveX n L
  let V : ℝ := primitiveEndpointVaughanBudget
    (powerSieveX n L) (2 * Q)
  let s : ℝ := Real.sqrt (n : ℝ)
  have hfinite' : (n : ℝ) * V ≤
      50 * K * x * (Q : ℝ) * Real.log x ^ 4 := by
    simpa only [K, x, V] using hfinite
  have hlogx : Real.log x =
      ((240 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
    dsimp [x, powerSieveX]
    rw [Nat.cast_pow, Real.log_pow]
  have hsSq : s * s = (n : ℝ) := by
    dsimp [s]
    rw [Real.mul_self_sqrt]
    positivity
  have hscaled :
      (n : ℝ) * (10 * s * V) ≤
        (n : ℝ) * ((Q : ℝ) * x) := by
    calc
      (n : ℝ) * (10 * s * V) = 10 * s * ((n : ℝ) * V) := by ring
      _ ≤ 10 * s *
          (50 * K * x * (Q : ℝ) * Real.log x ^ 4) := by gcongr
      _ = (B * Real.log (n : ℝ) ^ 4) * s * (Q : ℝ) * x := by
        rw [hlogx, mul_pow]
        dsimp [B]
        ring
      _ ≤ s * s * (Q : ℝ) * x := by gcongr
      _ = (n : ℝ) * ((Q : ℝ) * x) := by rw [hsSq]; ring
  have hnR : (0 : ℝ) < n := by positivity
  have hgoal := le_of_mul_le_mul_left hscaled hnR
  simpa only [s, V, x] using hgoal

/-- Both Vaughan estimates at the exact dyadic cutoffs, with no explicit
budget hypotheses.  The only density input is the natural comparison of
the block scale with `sqrt n` times the number of prime roots in the block. -/
theorem eventually_powerSieve_dyadicVaughanBudgets_absorbed
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      (20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicAuxCutoff n L Q) ≤
        (powerSieveDyadicPartnerLower n L Q : ℝ) *
          (powerSieveX n L : ℝ)) ∧
      (40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicProductCutoff n L Q) ≤
        ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          (powerSieveDyadicPartnerLower n L Q : ℝ) *
            (powerSieveX n L : ℝ)) := by
  have hbudget := eventually_powerSieve_twoVaughanBudgets_absorbed
    L 1000 hL (by norm_num)
  have hdensity := eventually_powerSieve_dyadicPrimeBlock_rootDensity L hL
  filter_upwards [hbudget, hdensity] with n hn hdensityN
  intro Q hQ hQupper
  have hrootDensity := hdensityN Q hQ hQupper
  have hbase := hn Q (powerSieveDyadicPrimeBlock Q).card
    hQ hQupper hrootDensity
  have hpartnerNat :=
    powerSieveVaughanPartnerThreshold_le_dyadicPartnerLower
      (n := n) (Q := Q) hL
  have hpartner :
      (powerSieveVaughanPartnerThreshold n L Q 1000 : ℝ) ≤
        (powerSieveDyadicPartnerLower n L Q : ℝ) := by
    exact_mod_cast hpartnerNat
  constructor
  · calc
      20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicAuxCutoff n L Q) =
        20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveAuxUpper n L Q) := rfl
      _ ≤ (powerSieveVaughanPartnerThreshold n L Q 1000 : ℝ) *
          (powerSieveX n L : ℝ) := hbase.1
      _ ≤ (powerSieveDyadicPartnerLower n L Q : ℝ) *
          (powerSieveX n L : ℝ) := by gcongr
  · have hbudgetMono :
        primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicProductCutoff n L Q) ≤
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveProductVaughanCutoff n L Q) :=
      primitiveEndpointVaughanBudget_mono_cutoff
        powerSieveDyadicProductCutoff_le_productVaughanCutoff
    calc
      40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicProductCutoff n L Q) ≤
        40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveProductVaughanCutoff n L Q) := by gcongr
      _ ≤ ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          (powerSieveVaughanPartnerThreshold n L Q 1000 : ℝ) *
            (powerSieveX n L : ℝ) := hbase.2
      _ ≤ ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          (powerSieveDyadicPartnerLower n L Q : ℝ) *
            (powerSieveX n L : ℝ) := by gcongr

/-- All three Vaughan budgets used by the endpoint-good/endpoint-bad
dyadic split. -/
theorem eventually_powerSieve_allDyadicVaughanBudgets_absorbed
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      ((20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicAuxCutoff n L Q) ≤
        (powerSieveDyadicPartnerLower n L Q : ℝ) *
          (powerSieveX n L : ℝ)) ∧
       (40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicProductCutoff n L Q) ≤
        ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          (powerSieveDyadicPartnerLower n L Q : ℝ) *
            (powerSieveX n L : ℝ))) ∧
      (n < 2 * Q →
        10 * Real.sqrt (n : ℝ) *
            primitiveEndpointVaughanBudget (powerSieveX n L) (2 * Q) ≤
          (Q : ℝ) * (powerSieveX n L : ℝ)) := by
  have hpair := eventually_powerSieve_dyadicVaughanBudgets_absorbed L hL
  have hroot := eventually_powerSieve_rootVaughanBudget_absorbed L hL
  filter_upwards [hpair, hroot] with n hpairN hrootN
  intro Q hQ hQupper
  exact ⟨hpairN Q hQ hQupper, hrootN Q hQ hQupper⟩

/-- Eventual dyadic cardinality bound with the two explicit Vaughan budget
premises discharged.  The remaining hypotheses are precisely the finite
bad-partner inputs of `powerSieveDyadicBadRoots_card_mul_sqrt_le_block`. -/
theorem eventually_powerSieveDyadicBadRoots_card_mul_sqrt_le_block
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop,
      ∀ Q B : ℕ, ∀ W : ℕ → ℝ, ∀ E : Finset ℕ,
      1 ≤ Q → Q ≤ powerSieveSmoothBound n L →
      E ⊆ powerSieveEndpointGoodDyadicBadRoots n L Q W →
      0 < powerSieveDyadicPartnerLower n L Q →
      (1 / (500 * (L : ℝ)) : ℝ) ≤
        ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹ →
      (∀ q ∈ E, 0 < W q) →
      (∀ q ∈ E, ∀ r ∈ powerSieveAuxPrimes n L Q,
        ∀ p ∈ primesInProgression
          (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B) →
      (∀ q ∈ E, ∀ r ∈ powerSieveAuxPrimes n L Q,
        ((representedLargeFactorPrimes
          (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
            W q * (r : ℝ)⁻¹ ≤
          powerSieveProgressionBudget (powerSieveX n L) q r) →
      ((E.card : ℕ) : ℝ) * Real.sqrt (n : ℝ) ≤
        ((powerSieveDyadicPrimeBlock Q).card : ℝ) := by
  have hbudgets := eventually_powerSieve_dyadicVaughanBudgets_absorbed L hL
  filter_upwards [hbudgets, eventually_ge_atTop 2] with n hbudget hn
  intro Q B W E hQ hQupper hE hpartnerPos hmass hW
    hcofactor hnumeric
  have hb := hbudget Q hQ hQupper
  have hx : 4 ≤ powerSieveX n L := by
    rw [powerSieveX_eq_auxScale_pow]
    have hscale : 2 ≤ powerSieveAuxScale n L := by
      simpa only [powerSieveAuxScale] using hn
    exact (by norm_num : 4 ≤ 2 ^ 2) |>.trans
      (Nat.pow_le_pow_left hscale 2) |>.trans
      (pow_le_pow_right' (by omega : 1 ≤ powerSieveAuxScale n L)
        (by omega : 2 ≤ 240 * L))
  apply badRoots_card_mul_sqrt_le_card_of_twoVaughanBudgets
    (x := powerSieveX n L)
    (Maux := powerSieveDyadicAuxCutoff n L Q)
    (Mprod := powerSieveDyadicProductCutoff n L Q)
    (A := powerSieveDyadicPartnerLower n L Q)
    (Q := powerSieveDyadicPrimeBlock Q)
    (R := powerSieveAuxPrimes n L Q)
    hx hpartnerPos
  · exact powerSieveDyadicAuxCutoff_le_sqrt hn hL hQ
  · exact powerSieveDyadicProductCutoff_le_sqrt hn hL hQupper
  · intro q hqE
    exact (mem_powerSieveEndpointGoodDyadicBadRoots.mp (hE hqE)).2.1
  · intro q hqBlock
    exact (mem_powerSieveDyadicPrimeBlock.mp hqBlock).2.2
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp hr).2.2
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp hr).2.1
  · intro q hqBlock r hr
    exact Nat.mul_le_mul
      (mem_powerSieveDyadicPrimeBlock.mp hqBlock).2.1
      (mem_powerSieveAuxPrimes.mp hr).2.1
  · intro q hqE
    have hqData := mem_powerSieveEndpointGoodDyadicBadRoots.mp (hE hqE)
    exact powerSieveDyadicPartnerLower_le_card_endpointBadAuxiliaryPartners
      hn hL hQ hmass (hW q hqE) hqData.1 hqData.2.2.1
      hqData.2.2.2 (hcofactor q hqE) (hnumeric q hqE)
  · exact hb.1
  · exact hb.2

end

end Erdos48
