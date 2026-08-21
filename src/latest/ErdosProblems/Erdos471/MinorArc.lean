/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos471.MajorMinor

/-!
# The minor-arc estimate for Erdős Problem 471

This file specializes the explicit Vaughan bound proved in `MajorMinor` to
the logarithmic circle-method cutoffs.  It derives a uniform
`O(n / logScale(n)^6)` pointwise estimate and, by Parseval, an
`o(n^2)` bound for the minor-arc integral.
-/

noncomputable section

namespace Erdos471.Analytic

open Filter

/-- The logarithmic factor used in the minor-arc estimate is eventually
dominated by the fifth root of the main parameter. -/
theorem eventually_eight_logScale_pow_100_le_rpow_fifth :
    ∀ᶠ n : ℕ in atTop,
      8 * (logScale n : ℝ) ^ 100 ≤ (n : ℝ) ^ ((1 : ℝ) / 5) := by
  let δ : ℝ := 1 / (8 * (3 : ℝ) ^ 100)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmallReal :=
    isLittleO_log_rpow_rpow_atTop (100 : ℝ)
      (show (0 : ℝ) < (1 : ℝ) / 5 by norm_num)
  have hsmallNat := hsmallReal.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hsmallNat.bound hδ
  filter_upwards [hsmall, eventually_ge_atTop (4 : ℕ)] with n hnsmall hn4
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hnsmall' : Real.log (n : ℝ) ^ (100 : ℝ) ≤
      δ * (n : ℝ) ^ ((1 : ℝ) / 5) := by
    change |Real.log (n : ℝ) ^ (100 : ℝ)| ≤
      δ * |(n : ℝ) ^ ((1 : ℝ) / 5)| at hnsmall
    rw [abs_of_nonneg (Real.rpow_nonneg hlog0 _),
      abs_of_nonneg (Real.rpow_nonneg hnR.le _)] at hnsmall
    exact hnsmall
  have hlogNat : Real.log (n : ℝ) ^ (100 : ℝ) =
      Real.log (n : ℝ) ^ (100 : ℕ) := by norm_num
  rw [hlogNat] at hnsmall'
  have hLlog : (logScale n : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    simpa [logScale] using Erdos387.binaryLogScale_cast_le_three_mul_log hn4
  have hL100 : (logScale n : ℝ) ^ 100 ≤
      (3 : ℝ) ^ 100 * Real.log (n : ℝ) ^ 100 := by
    calc
      (logScale n : ℝ) ^ 100 ≤ (3 * Real.log (n : ℝ)) ^ 100 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hLlog 100
      _ = (3 : ℝ) ^ 100 * Real.log (n : ℝ) ^ 100 := by rw [mul_pow]
  have hmul := mul_le_mul_of_nonneg_left hnsmall'
    (show 0 ≤ 8 * (3 : ℝ) ^ 100 by positivity)
  dsimp [δ] at hmul
  have hcancel : 8 * (3 : ℝ) ^ 100 *
      (1 / (8 * (3 : ℝ) ^ 100) * (n : ℝ) ^ ((1 : ℝ) / 5)) =
    (n : ℝ) ^ ((1 : ℝ) / 5) := by field_simp
  calc
    8 * (logScale n : ℝ) ^ 100 ≤
        8 * ((3 : ℝ) ^ 100 * Real.log (n : ℝ) ^ 100) := by gcongr
    _ = (8 * (3 : ℝ) ^ 100) * Real.log (n : ℝ) ^ 100 := by ring
    _ ≤ (8 * (3 : ℝ) ^ 100) *
        (1 / (8 * (3 : ℝ) ^ 100) * (n : ℝ) ^ ((1 : ℝ) / 5)) := hmul
    _ = (n : ℝ) ^ ((1 : ℝ) / 5) := hcancel

private theorem sqrt_majorDenominatorCutoff (n : ℕ) :
    Real.sqrt (majorDenominatorCutoff n : ℝ) =
      (logScale n : ℝ) ^ 10 := by
  have hL0 : 0 ≤ (logScale n : ℝ) := Nat.cast_nonneg _
  change Real.sqrt (((logScale n ^ 20 : ℕ) : ℝ)) = (logScale n : ℝ) ^ 10
  rw [Nat.cast_pow]
  have hpow : (logScale n : ℝ) ^ 20 = ((logScale n : ℝ) ^ 10) ^ 2 := by ring
  rw [hpow, Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hL0 _)]

private theorem sqrt_dirichlet_mul_logScale_pow_le (n : ℕ) :
    Real.sqrt ((dirichletCutoff n : ℝ) * n) * (logScale n : ℝ) ^ 50 ≤
      (n : ℝ) := by
  let L : ℝ := logScale n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by dsimp [L]; exact_mod_cast Nat.zero_le (logScale n)
  have hDLnat : dirichletCutoff n * logScale n ^ 100 ≤ n := by
    simpa [dirichletCutoff] using
      (Nat.div_mul_le_self n (logScale n ^ 100))
  have hDL : (dirichletCutoff n : ℝ) * L ^ 100 ≤ (n : ℝ) := by
    dsimp [L]
    exact_mod_cast hDLnat
  have hleft0 : 0 ≤ Real.sqrt ((dirichletCutoff n : ℝ) * n) * L ^ 50 :=
    mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hL0 _)
  apply (sq_le_sq₀ hleft0 hn0).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) hn0)]
  have hpow : (L ^ 50) ^ 2 = L ^ 100 := by ring
  rw [hpow]
  calc
    ((dirichletCutoff n : ℝ) * (n : ℝ)) * L ^ 100 =
        ((dirichletCutoff n : ℝ) * L ^ 100) * (n : ℝ) := by ring
    _ ≤ (n : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hDL hn0
    _ = (n : ℝ) ^ 2 := by ring

private theorem rpow_four_fifths_mul_logScale_pow_four_le
    {n : ℕ} (hn : 1 ≤ n)
    (hscale : 8 * (logScale n : ℝ) ^ 100 ≤
      (n : ℝ) ^ ((1 : ℝ) / 5)) :
    (n : ℝ) ^ ((4 : ℝ) / 5) * (logScale n : ℝ) ^ 4 ≤
      (n : ℝ) / (logScale n : ℝ) ^ 6 := by
  let L : ℝ := logScale n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hLone : (1 : ℝ) ≤ L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hL10 : L ^ 10 ≤ 8 * L ^ 100 := by
    have hpow : L ^ 10 ≤ L ^ 100 := by
      calc
        L ^ 10 = L ^ 10 * 1 := by ring
        _ ≤ L ^ 10 * L ^ 90 := by
          gcongr
          exact one_le_pow₀ hLone
        _ = L ^ 100 := by ring
    exact hpow.trans (by
      have hnonneg : 0 ≤ L ^ 100 := pow_nonneg hLpos.le _
      linarith)
  have hrpowProd : (n : ℝ) ^ ((4 : ℝ) / 5) * L ^ 10 ≤ (n : ℝ) := by
    calc
      (n : ℝ) ^ ((4 : ℝ) / 5) * L ^ 10 ≤
          (n : ℝ) ^ ((4 : ℝ) / 5) * (8 * L ^ 100) := by gcongr
      _ ≤ (n : ℝ) ^ ((4 : ℝ) / 5) *
          (n : ℝ) ^ ((1 : ℝ) / 5) := by
        dsimp [L] at hscale ⊢
        gcongr
      _ = (n : ℝ) := by
        rw [← Real.rpow_add hnR]
        norm_num
  apply (le_div_iff₀ (pow_pos hLpos 6)).2
  calc
    (n : ℝ) ^ ((4 : ℝ) / 5) * L ^ 4 * L ^ 6 =
        (n : ℝ) ^ ((4 : ℝ) / 5) * L ^ 10 := by ring
    _ ≤ (n : ℝ) := hrpowProd

private lemma first_log_term_le {n : ℕ} {L : ℝ}
    (hLpos : 0 < L)
    (hlog4 : Real.log (n : ℝ) ^ 4 ≤ (4 * L) ^ 4) :
    ((n : ℝ) / L ^ 10) * Real.log (n : ℝ) ^ 4 ≤
      256 * ((n : ℝ) / L ^ 6) := by
  calc
    ((n : ℝ) / L ^ 10) * Real.log (n : ℝ) ^ 4 ≤
        ((n : ℝ) / L ^ 10) * (4 * L) ^ 4 :=
      mul_le_mul_of_nonneg_left hlog4
        (div_nonneg (Nat.cast_nonneg _) (by positivity))
    _ = 256 * ((n : ℝ) / L ^ 6) := by
      field_simp [hLpos.ne']
      ring

private lemma middle_log_term_le {n : ℕ} {L : ℝ}
    (hlog4 : Real.log (n : ℝ) ^ 4 ≤ (4 * L) ^ 4)
    (hrpowL4 : (n : ℝ) ^ ((4 : ℝ) / 5) * L ^ 4 ≤
      (n : ℝ) / L ^ 6) :
    (n : ℝ) ^ ((4 : ℝ) / 5) * Real.log (n : ℝ) ^ 4 ≤
      256 * ((n : ℝ) / L ^ 6) := by
  have hr0 : 0 ≤ (n : ℝ) ^ ((4 : ℝ) / 5) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    (n : ℝ) ^ ((4 : ℝ) / 5) * Real.log (n : ℝ) ^ 4 ≤
        (n : ℝ) ^ ((4 : ℝ) / 5) * (4 * L) ^ 4 :=
      mul_le_mul_of_nonneg_left hlog4 hr0
    _ = 256 * ((n : ℝ) ^ ((4 : ℝ) / 5) * L ^ 4) := by ring
    _ ≤ 256 * ((n : ℝ) / L ^ 6) :=
      mul_le_mul_of_nonneg_left hrpowL4 (by norm_num)

private lemma div_pow_mono {n : ℕ} {L : ℝ} (hLone : 1 ≤ L)
    {a b : ℕ} (hab : a ≤ b) :
    (n : ℝ) / L ^ b ≤ (n : ℝ) / L ^ a := by
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    (pow_pos (lt_of_lt_of_le zero_lt_one hLone) a)
  have hpow : L ^ b = L ^ a * L ^ (b - a) := by
    rw [← pow_add]
    congr
    omega
  rw [hpow]
  exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hLone) _)
    (one_le_pow₀ hLone)

private lemma last_log_term_le {n D : ℕ} {L : ℝ}
    (hLpos : 0 < L) (hLone : 1 ≤ L)
    (hlog4 : Real.log (n : ℝ) ^ 4 ≤ (4 * L) ^ 4)
    (hsqrtD : Real.sqrt ((D : ℝ) * n) ≤ (n : ℝ) / L ^ 50) :
    Real.sqrt ((D : ℝ) * n) * Real.log (n : ℝ) ^ 4 ≤
      256 * ((n : ℝ) / L ^ 6) := by
  have hratio := div_pow_mono (n := n) hLone (a := 6) (b := 46) (by omega)
  calc
    Real.sqrt ((D : ℝ) * n) * Real.log (n : ℝ) ^ 4 ≤
        ((n : ℝ) / L ^ 50) * (4 * L) ^ 4 :=
      mul_le_mul hsqrtD hlog4 (by positivity)
        (div_nonneg (Nat.cast_nonneg _) (by positivity))
    _ = 256 * ((n : ℝ) / L ^ 46) := by
      field_simp [hLpos.ne']
      ring
    _ ≤ 256 * ((n : ℝ) / L ^ 6) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)

private lemma D_log_term_le {n D : ℕ} {L : ℝ}
    (hLpos : 0 < L) (hLone : 1 ≤ L)
    (hlog0 : 0 ≤ Real.log (n : ℝ)) (hlog : Real.log (n : ℝ) ≤ 4 * L)
    (hD : (D : ℝ) ≤ (n : ℝ) / L ^ 100) :
    2 * (D : ℝ) * Real.log (n : ℝ) ≤ 8 * ((n : ℝ) / L ^ 6) := by
  have hratio := div_pow_mono (n := n) hLone (a := 6) (b := 99) (by omega)
  calc
    2 * (D : ℝ) * Real.log (n : ℝ) ≤
        2 * ((n : ℝ) / L ^ 100) * (4 * L) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hD (by norm_num)) hlog
        hlog0 (mul_nonneg (by norm_num)
          (div_nonneg (Nat.cast_nonneg _) (by positivity)))
    _ = 8 * ((n : ℝ) / L ^ 99) := by
      field_simp [hLpos.ne']
      ring
    _ ≤ 8 * ((n : ℝ) / L ^ 6) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)

private theorem vaughan_rhs_le
    {n : ℕ} (hn : 1 ≤ n)
    (hscale : 8 * (logScale n : ℝ) ^ 100 ≤
      (n : ℝ) ^ ((1 : ℝ) / 5)) :
    2304 * (((n : ℝ) / Real.sqrt (majorDenominatorCutoff n : ℝ) +
        (n : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((dirichletCutoff n : ℝ) * n)) *
          Real.log (n : ℝ) ^ 4) +
        2 * (dirichletCutoff n : ℝ) * Real.log (n : ℝ) ≤
      2000000 * (n : ℝ) / (logScale n : ℝ) ^ 6 := by
  let L : ℝ := logScale n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hLone : (1 : ℝ) ≤ L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hsqrtP : Real.sqrt (majorDenominatorCutoff n : ℝ) = L ^ 10 := by
    change Real.sqrt (majorDenominatorCutoff n : ℝ) =
      (logScale n : ℝ) ^ 10
    exact sqrt_majorDenominatorCutoff n
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hlog : Real.log (n : ℝ) ≤ 4 * L := by
    have hmono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log hnR (by linarith)
    have hs := log_succ_add_one_le_four_logScale hn
    dsimp [L] at hs ⊢
    linarith
  have hlog4 : Real.log (n : ℝ) ^ 4 ≤ (4 * L) ^ 4 :=
    pow_le_pow_left₀ hlog0 hlog 4
  have hDLnat : dirichletCutoff n * logScale n ^ 100 ≤ n := by
    simpa [dirichletCutoff] using
      (Nat.div_mul_le_self n (logScale n ^ 100))
  have hDL : (dirichletCutoff n : ℝ) * L ^ 100 ≤ (n : ℝ) := by
    dsimp [L]
    exact_mod_cast hDLnat
  have hsqrtDmul : Real.sqrt ((dirichletCutoff n : ℝ) * n) * L ^ 50 ≤
      (n : ℝ) := by
    change Real.sqrt ((dirichletCutoff n : ℝ) * n) *
      (logScale n : ℝ) ^ 50 ≤ (n : ℝ)
    exact sqrt_dirichlet_mul_logScale_pow_le n
  have hsqrtD : Real.sqrt ((dirichletCutoff n : ℝ) * n) ≤
      (n : ℝ) / L ^ 50 :=
    (le_div_iff₀ (pow_pos hLpos 50)).2 hsqrtDmul
  have hrpowL4 : (n : ℝ) ^ ((4 : ℝ) / 5) * L ^ 4 ≤
      (n : ℝ) / L ^ 6 := by
    change (n : ℝ) ^ ((4 : ℝ) / 5) * (logScale n : ℝ) ^ 4 ≤
      (n : ℝ) / (logScale n : ℝ) ^ 6
    exact rpow_four_fifths_mul_logScale_pow_four_le hn hscale
  have hfirst : ((n : ℝ) / Real.sqrt (majorDenominatorCutoff n : ℝ)) *
      Real.log (n : ℝ) ^ 4 ≤ 256 * ((n : ℝ) / L ^ 6) := by
    rw [hsqrtP]
    exact first_log_term_le hLpos hlog4
  have hmiddle : (n : ℝ) ^ ((4 : ℝ) / 5) * Real.log (n : ℝ) ^ 4 ≤
      256 * ((n : ℝ) / L ^ 6) :=
    middle_log_term_le hlog4 hrpowL4
  have hlast : Real.sqrt ((dirichletCutoff n : ℝ) * n) *
      Real.log (n : ℝ) ^ 4 ≤ 256 * ((n : ℝ) / L ^ 6) :=
    last_log_term_le hLpos hLone hlog4 hsqrtD
  have hmain : (((n : ℝ) / Real.sqrt (majorDenominatorCutoff n : ℝ) +
        (n : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((dirichletCutoff n : ℝ) * n)) *
      Real.log (n : ℝ) ^ 4) ≤ 768 * ((n : ℝ) / L ^ 6) := by
    rw [add_mul, add_mul]
    linarith
  have hDratio : (dirichletCutoff n : ℝ) ≤ (n : ℝ) / L ^ 100 :=
    (le_div_iff₀ (pow_pos hLpos 100)).2 hDL
  have hDlog : 2 * (dirichletCutoff n : ℝ) * Real.log (n : ℝ) ≤
      8 * ((n : ℝ) / L ^ 6) :=
    D_log_term_le hLpos hLone hlog0 hlog hDratio
  calc
    2304 * (((n : ℝ) / Real.sqrt (majorDenominatorCutoff n : ℝ) +
        (n : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((dirichletCutoff n : ℝ) * n)) *
          Real.log (n : ℝ) ^ 4) +
        2 * (dirichletCutoff n : ℝ) * Real.log (n : ℝ) ≤
      2304 * (768 * ((n : ℝ) / L ^ 6)) +
        8 * ((n : ℝ) / L ^ 6) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num)) hDlog
    _ ≤ 2000000 * (n : ℝ) / L ^ 6 := by
      have hU : 0 ≤ (n : ℝ) / L ^ 6 :=
        div_nonneg (Nat.cast_nonneg _) (pow_nonneg hLpos.le _)
      rw [show 2000000 * (n : ℝ) / L ^ 6 =
        2000000 * ((n : ℝ) / L ^ 6) by ring]
      nlinarith

/-- The explicit minor-arc exponential-sum bound at the logarithmic cutoffs. -/
theorem minor_pointwise_bound
    {n : ℕ} (hn32 : 32 ≤ n)
    (hscale : 8 * (logScale n : ℝ) ^ 100 ≤
      (n : ℝ) ^ ((1 : ℝ) / 5))
    (hV : 4 * (n : ℝ) ^ ((3 : ℝ) / 5) ≤ (dirichletCutoff n : ℝ) ∧
      2 * (MathExtras.Helfgott.vaughanCutoff n *
        MathExtras.Helfgott.vaughanCutoff n) ≤ dirichletCutoff n)
    {α : ℝ} (hα : α ∈ torusMinorArcs (dirichletCutoff n)
      (majorDenominatorCutoff n)) :
    ‖Vinogradov.vonMangoldtExpSum α n‖ ≤
      2000000 * (n : ℝ) / (logScale n : ℝ) ^ 6 := by
  have hn : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hP : 1 ≤ majorDenominatorCutoff n :=
    pow_pos (Erdos387.binaryLogScale_pos n) _
  have hDpos : 0 < dirichletCutoff n := by
    by_contra hD
    have hD0 : dirichletCutoff n = 0 := Nat.eq_zero_of_not_pos hD
    rw [hD0] at hV
    norm_num at hV
    have : 0 < (n : ℝ) ^ ((3 : ℝ) / 5) := Real.rpow_pos_of_pos hnR _
    linarith
  exact (norm_vonMangoldtExpSum_minor_le hn32 hDpos hP
    (dirichletCutoff_le n) hV.1 hV.2 hα).trans
      (vaughan_rhs_le hn hscale)

private theorem minor_parseval_factor_le {n : ℕ} (hn : 1 ≤ n) :
    (((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ 2) ≤
      32 * (n : ℝ) * (logScale n : ℝ) ^ 2 := by
  let L : ℝ := logScale n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (((n + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by linarith [hnR])
  have hlog : Real.log ((n : ℝ) + 1) ≤ 4 * L := by
    have hs := log_succ_add_one_le_four_logScale hn
    dsimp [L] at hs ⊢
    linarith
  calc
    (((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ 2) ≤
        (2 * (n : ℝ)) * (4 * L) ^ 2 :=
      mul_le_mul hn1 (pow_le_pow_left₀ hlog0 hlog 2)
        (sq_nonneg _) (by positivity)
    _ = 32 * (n : ℝ) * L ^ 2 := by ring

/-- Parseval turns the pointwise Vaughan saving into a concrete
`O(n^2 / logScale(n)^4)` minor-arc bound. -/
theorem minor_integral_envelope_le
    {n : ℕ} (hn32 : 32 ≤ n)
    (hscale : 8 * (logScale n : ℝ) ^ 100 ≤
      (n : ℝ) ^ ((1 : ℝ) / 5))
    (hV : 4 * (n : ℝ) ^ ((3 : ℝ) / 5) ≤ (dirichletCutoff n : ℝ) ∧
      2 * (MathExtras.Helfgott.vaughanCutoff n *
        MathExtras.Helfgott.vaughanCutoff n) ≤ dirichletCutoff n) :
    ‖∫ α in torusMinorArcs (dirichletCutoff n)
        (majorDenominatorCutoff n), integrand n α‖ ≤
      64000000 * (n : ℝ) ^ 2 / (logScale n : ℝ) ^ 4 := by
  let L : ℝ := logScale n
  let B : ℝ := 2000000 * (n : ℝ) / L ^ 6
  have hn : 1 ≤ n := by omega
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (pow_nonneg hLpos.le _)
  have hpoint : ∀ α ∈ torusMinorArcs (dirichletCutoff n)
      (majorDenominatorCutoff n),
      ‖Vinogradov.vonMangoldtExpSum α n‖ ≤ B := by
    intro α hα
    dsimp [B, L]
    exact minor_pointwise_bound hn32 hscale hV hα
  have hbase := norm_minor_integral_le hB hpoint
  have hfactor := minor_parseval_factor_le hn
  calc
    ‖∫ α in torusMinorArcs (dirichletCutoff n)
        (majorDenominatorCutoff n), integrand n α‖ ≤
      B * (((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ 2) := hbase
    _ ≤ B * (32 * (n : ℝ) * L ^ 2) :=
      mul_le_mul_of_nonneg_left hfactor hB
    _ = 64000000 * (n : ℝ) ^ 2 / L ^ 4 := by
      dsimp [B]
      field_simp [hLpos.ne']
      ring

/-- The minor-arc integral is `o(n^2)` at the chosen cutoffs. -/
theorem eventually_norm_minor_integral_le_mul
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖∫ α in torusMinorArcs (dirichletCutoff n)
          (majorDenominatorCutoff n), integrand n α‖ ≤
        ε * (n : ℝ) ^ 2 := by
  let C : ℝ := 64000000 / ε
  have hC : 0 < C := by dsimp [C]; positivity
  have hL4Nat : Tendsto (fun n : ℕ => logScale n ^ 4) atTop atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : 4 ≠ 0)).comp tendsto_logScale
  have hL4 : Tendsto (fun n : ℕ => ((logScale n ^ 4 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hL4Nat
  have hlarge := hL4.eventually_ge_atTop C
  filter_upwards [eventually_eight_logScale_pow_100_le_rpow_fifth,
    eventually_dirichletCutoff_vaughan_conditions,
    eventually_ge_atTop (32 : ℕ), hlarge]
      with n hscale hV hn32 hlarge
  have hLpos : (0 : ℝ) < logScale n := by
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hlarge' : C ≤ (logScale n : ℝ) ^ 4 := by
    simpa only [Nat.cast_pow] using hlarge
  have hden : 64000000 ≤ ε * (logScale n : ℝ) ^ 4 := by
    have := (div_le_iff₀ hε).mp (by simpa [C] using hlarge')
    simpa [mul_comm] using this
  have hratio : 64000000 / (logScale n : ℝ) ^ 4 ≤ ε := by
    rw [div_le_iff₀ (pow_pos hLpos 4)]
    exact hden
  exact (minor_integral_envelope_le hn32 hscale hV).trans (by
    calc
      64000000 * (n : ℝ) ^ 2 / (logScale n : ℝ) ^ 4 =
          (64000000 / (logScale n : ℝ) ^ 4) * (n : ℝ) ^ 2 := by ring
      _ ≤ ε * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hratio (sq_nonneg _))

end Erdos471.Analytic
