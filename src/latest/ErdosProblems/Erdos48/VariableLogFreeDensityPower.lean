/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.VariableLogFreeDensity

/-!
# A power-form variable log-free zero-density estimate

The detector envelope is explicit but retains its order, propagation radius,
and truncation cutoff.  This file eliminates those auxiliary parameters.  If
the rectangle width is at least a fixed positive multiple of `1 / log B`, the
only negative powers of the width cost three powers of `log B`; every factor
exponential in the detector order is absorbed by `B ^ (c * eta)`.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

theorem nat_pow_le_exp_of_cast_le
    {a u : ℝ} {n : ℕ} (ha : 1 ≤ a) (hn : (n : ℝ) ≤ u) :
    a ^ n ≤ Real.exp (Real.log a * u) := by
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha
  calc
    a ^ n = Real.exp (Real.log a * (n : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one ha)]
    _ ≤ Real.exp (Real.log a * u) := by
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left hn hlog

theorem add_two_le_exp_add_two {h : ℝ} :
    h + 2 ≤ Real.exp (h + 2) := by
  have := Real.add_one_le_exp (h + 2)
  linarith

private theorem exp_pow_two (x : ℝ) :
    Real.exp x ^ 2 = Real.exp (2 * x) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

private theorem exp_mul_exp (x y : ℝ) :
    Real.exp x * Real.exp y = Real.exp (x + y) := by
  rw [Real.exp_add]

private theorem exp_mul_exp_mul_exp (x y z : ℝ) :
    Real.exp x * Real.exp y * Real.exp z = Real.exp (x + y + z) := by
  rw [Real.exp_add, Real.exp_add]

private theorem envelope_coefficient_rearrangement
    (p env eta e₁ e₂ e₃ : ℝ) :
    e₁ * (4 * p ^ 2 * e₂) *
        (env * (4 * p ^ 2 * e₃ / eta ^ 2)) =
      (16 * p ^ 4) * env / eta ^ 2 *
        (e₁ * e₂ * e₃) := by
  ring

private theorem density_coefficient_growth_rearrangement
    (k a C₀ p env eta q x y : ℝ) :
    256 * (k * Real.exp x) * ((a + 1) * Real.exp x) *
        (a * Real.exp x) * (12 * C₀) * q *
        (((16 * p ^ 4) * env / eta ^ 2) *
          Real.exp y) / eta =
      (256 * k * (a + 1) * a * (12 * C₀) *
          (16 * p ^ 4) * env) / eta ^ 3 *
        (q * Real.exp (3 * x + y)) := by
  have he : Real.exp x * Real.exp x * Real.exp x * Real.exp y =
      Real.exp (3 * x + y) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [← he]
  ring

/-- All order, propagation, and cutoff estimates needed to simplify the raw
variable-density envelope.  Keeping this as a separate declaration gives the
elementary parameter reduction its own kernel-checking budget. -/
theorem variable_envelope_parameter_bounds
    {κ D A Q T : ℕ} (hκ : 1 ≤ κ) (hD : 1 ≤ D)
    (hQ : 2 ≤ Q) (hT : 2 ≤ T)
    {eta : ℝ} (heta : 0 < eta) (heta8 : eta ≤ 1 / 8) :
    let E : ℕ := D + κ
    let a : ℕ := (D + κ) * variableDetectorHeightDilation E
    let C₀ : ℝ := Real.log 4 + 4
    let cTail : ℝ := 12 * C₀
    let rCoeff : ℝ := 4 * (Real.log (1 + cTail) + Real.log 4624)
    let pCoeff : ℝ := rCoeff * (a : ℝ) + 1
    let kCoeff : ℝ := 32 * C₀ + 256 * (A : ℝ) / 3
    let envCoeff : ℝ := 2 * Real.exp 2 * (1 + 8 * Real.pi)
    let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
    let h : ℝ := eta * Real.log B
    let H₀ : ℕ := Nat.ceil (1 + h)
    let H : ℕ := variableDetectorHeightDilation E * H₀
    let J : ℕ := (D + κ) * H
    let R : ℝ := variableZeroDetectorTailRadius J
    let N : ℕ := zeroDetectorCutoff R eta
    let Klocal : ℝ := 32 * C₀ + (256 * (A : ℝ) / 3) * h
    1 ≤ J ∧
      (J : ℝ) ≤ (a : ℝ) * (h + 2) ∧
      (J : ℝ) ≤ (a : ℝ) * Real.exp (h + 2) ∧
      ((J + 1 : ℕ) : ℝ) ≤ ((a : ℝ) + 1) * Real.exp (h + 2) ∧
      Klocal ≤ kCoeff * Real.exp (h + 2) ∧
      variableLogFreeDensityEnvelope T N J eta ≤
        (16 * pCoeff ^ 4) * envCoeff / eta ^ 2 *
          Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
            4 * pCoeff + 4) * (h + 2)) := by
  let E : ℕ := D + κ
  let a : ℕ := (D + κ) * variableDetectorHeightDilation E
  let C₀ : ℝ := Real.log 4 + 4
  let cTail : ℝ := 12 * C₀
  let rCoeff : ℝ := 4 * (Real.log (1 + cTail) + Real.log 4624)
  let pCoeff : ℝ := rCoeff * (a : ℝ) + 1
  let kCoeff : ℝ := 32 * C₀ + 256 * (A : ℝ) / 3
  let envCoeff : ℝ := 2 * Real.exp 2 * (1 + 8 * Real.pi)
  have haNat : 1 ≤ a := by
    dsimp [a, E]
    exact Nat.mul_pos (by omega) (variableDetectorHeightDilation_pos (D + κ))
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast haNat
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hcTail : 0 < cTail := by dsimp [cTail]; positivity
  have hrCoeff : 0 < rCoeff := by
    dsimp [rCoeff]
    have hlogOne : 0 < Real.log (1 + cTail) :=
      Real.log_pos (by linarith)
    have hlogBase : 0 < Real.log (4624 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hpCoeff : 0 < pCoeff := by dsimp [pCoeff]; positivity
  have hkCoeff : 0 < kCoeff := by dsimp [kCoeff]; positivity
  have henvCoeff : 0 < envCoeff := by dsimp [envCoeff]; positivity
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let h : ℝ := eta * Real.log B
  let H₀ : ℕ := Nat.ceil (1 + h)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let P : ℝ := variableDetectorDyadicLength N
  let M : ℝ := ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)
  let Klocal : ℝ := 32 * C₀ + (256 * (A : ℝ) / 3) * h
  have hB8 : (8 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlogB : 0 < Real.log B :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 8) hB8)
  have hh : 0 < h := by dsimp [h]; positivity
  have hH₀ : ((H₀ : ℕ) : ℝ) ≤ h + 2 := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 1 + h by positivity)
    dsimp [H₀]
    linarith
  have hJEq : J = a * H₀ := by
    dsimp [J, H, a]
    rw [mul_assoc]
  have hJ : 1 ≤ J := by
    rw [hJEq]
    apply Nat.mul_pos haNat
    have hceil : (1 : ℝ) ≤ (H₀ : ℕ) := by
      have hone : (1 : ℝ) ≤ 1 + h := by linarith
      exact hone.trans (by simpa only [H₀] using Nat.le_ceil (1 + h))
    exact_mod_cast hceil
  have hJbound : (J : ℝ) ≤ (a : ℝ) * (h + 2) := by
    rw [hJEq]
    push_cast
    exact mul_le_mul_of_nonneg_left hH₀ (by positivity)
  have hJexp : (J : ℝ) ≤ (a : ℝ) * Real.exp (h + 2) := by
    exact hJbound.trans (mul_le_mul_of_nonneg_left
      add_two_le_exp_add_two (by positivity))
  have hJoneExp : ((J + 1 : ℕ) : ℝ) ≤
      ((a : ℝ) + 1) * Real.exp (h + 2) := by
    push_cast
    have hexpOne : (1 : ℝ) ≤ Real.exp (h + 2) :=
      Real.one_le_exp (by linarith)
    nlinarith
  have hR : R ≤ rCoeff * (J : ℝ) := by
    have hpowOne : (1 : ℝ) ≤ (4624 : ℝ) ^ J := one_le_pow₀ (by norm_num)
    have hinside :
        1 + cTail * (4624 : ℝ) ^ J ≤
          (1 + cTail) * (4624 : ℝ) ^ J := by
      calc
        1 + cTail * (4624 : ℝ) ^ J ≤
            (4624 : ℝ) ^ J + cTail * (4624 : ℝ) ^ J := by gcongr
        _ = (1 + cTail) * (4624 : ℝ) ^ J := by ring
    have hinsidePos : 0 < 1 + cTail * (4624 : ℝ) ^ J := by positivity
    have hlog := Real.log_le_log hinsidePos hinside
    have hlogPow : Real.log ((4624 : ℝ) ^ J) =
        (J : ℝ) * Real.log 4624 := Real.log_pow 4624 J
    have hlogsNonneg : 0 ≤ Real.log (1 + cTail) :=
      Real.log_nonneg (by linarith)
    have hlog4624 : 0 ≤ Real.log (4624 : ℝ) :=
      Real.log_nonneg (by norm_num)
    calc
      R = 4 * Real.log (1 + cTail * (4624 : ℝ) ^ J) := by
        simp only [R, variableZeroDetectorTailRadius, cTail, C₀]
      _ ≤ 4 * Real.log ((1 + cTail) * (4624 : ℝ) ^ J) := by gcongr
      _ = 4 * (Real.log (1 + cTail) +
          (J : ℝ) * Real.log 4624) := by
        rw [Real.log_mul (by positivity) (by positivity), hlogPow]
      _ ≤ 4 * ((Real.log (1 + cTail) + Real.log 4624) * (J : ℝ)) := by
        have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
        nlinarith
      _ = rCoeff * (J : ℝ) := by dsimp [rCoeff]; ring
  have hRbound : R ≤ rCoeff * (a : ℝ) * (h + 2) := by
    calc
      R ≤ rCoeff * (J : ℝ) := hR
      _ ≤ rCoeff * ((a : ℝ) * (h + 2)) := by gcongr
      _ = _ := by ring
  have hPraw : P ≤ R / eta + 2 := by
    simpa only [P, N, R] using
      variableDetectorDyadicLength_zeroDetectorCutoff_le
        (variableZeroDetectorTailRadius_pos J).le heta
  have hetaP : eta * P ≤ pCoeff * (h + 2) := by
    have hmul := mul_le_mul_of_nonneg_left hPraw heta.le
    have hetaR : eta * (R / eta + 2) = R + 2 * eta := by
      field_simp
    rw [hetaR] at hmul
    calc
      eta * P ≤ R + 2 * eta := hmul
      _ ≤ rCoeff * (a : ℝ) * (h + 2) + 1 / 4 := by
        have : 2 * eta ≤ 1 / 4 := by linarith
        linarith
      _ ≤ (rCoeff * (a : ℝ) + 1) * (h + 2) := by
        nlinarith [mul_nonneg hrCoeff.le (by positivity : (0 : ℝ) ≤ a)]
      _ = pCoeff * (h + 2) := rfl
  have hMlog : M * Real.log 2 = P := by
    rfl
  have hMhalf : M / 2 ≤ P := by
    rw [← hMlog]
    have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
    nlinarith [Real.log_two_gt_d9]
  have hetaM : eta * M ≤ 2 * pCoeff * (h + 2) := by
    have hMle : M ≤ 2 * P := by linarith
    calc
      eta * M ≤ eta * (2 * P) := by gcongr
      _ = 2 * (eta * P) := by ring
      _ ≤ 2 * (pCoeff * (h + 2)) := by gcongr
      _ = _ := by ring
  have hMbound : M ≤
      (2 * pCoeff * Real.exp (h + 2)) / eta := by
    apply (le_div_iff₀ heta).2
    calc
      M * eta = eta * M := by ring
      _ ≤ 2 * pCoeff * (h + 2) := hetaM
      _ ≤ 2 * pCoeff * Real.exp (h + 2) :=
        mul_le_mul_of_nonneg_left add_two_le_exp_add_two (by positivity)
  have hKlocal : Klocal ≤ kCoeff * Real.exp (h + 2) := by
    have hpre : Klocal ≤ kCoeff * (h + 2) := by
      let k₀ : ℝ := 32 * C₀
      let k₁ : ℝ := 256 * (A : ℝ) / 3
      have hk₀ : 0 ≤ k₀ := by dsimp [k₀]; positivity
      have hk₁ : 0 ≤ k₁ := by dsimp [k₁]; positivity
      have hdiff : 0 ≤ k₀ * (h + 1) + 2 * k₁ := by positivity
      have hsmall : k₀ + k₁ * h ≤ (k₀ + k₁) * (h + 2) := by
        calc
          k₀ + k₁ * h ≤
              k₀ + k₁ * h + (k₀ * (h + 1) + 2 * k₁) :=
            le_add_of_nonneg_right hdiff
          _ = (k₀ + k₁) * (h + 2) := by ring
      simpa only [Klocal, kCoeff, k₀, k₁] using hsmall
    exact hpre.trans (mul_le_mul_of_nonneg_left
      add_two_le_exp_add_two hkCoeff.le)
  have hdetector :
      ((2 * eta * P) * Real.exp (2 * eta * P)) ^ 2 ≤
        (4 * pCoeff ^ 2) * Real.exp ((2 + 4 * pCoeff) * (h + 2)) := by
    have hx : 0 ≤ 2 * eta * P := by
      dsimp [P, variableDetectorDyadicLength]
      positivity
    have hxBound : 2 * eta * P ≤ 2 * pCoeff * (h + 2) := by
      linarith
    have hxExp : 2 * eta * P ≤ 2 * pCoeff * Real.exp (h + 2) :=
      hxBound.trans (mul_le_mul_of_nonneg_left
        add_two_le_exp_add_two (by positivity))
    have hexpBound : Real.exp (2 * eta * P) ≤
        Real.exp (2 * pCoeff * (h + 2)) := Real.exp_le_exp.mpr hxBound
    calc
      ((2 * eta * P) * Real.exp (2 * eta * P)) ^ 2 ≤
          ((2 * pCoeff * Real.exp (h + 2)) *
            Real.exp (2 * pCoeff * (h + 2))) ^ 2 := by gcongr
      _ = (4 * pCoeff ^ 2) *
          Real.exp ((2 + 4 * pCoeff) * (h + 2)) := by
        rw [mul_pow, mul_pow, exp_pow_two, exp_pow_two]
        have heexp :
            Real.exp (2 * (2 * pCoeff * (h + 2))) =
              Real.exp (4 * pCoeff * (h + 2)) := by
          congr 1
          ring
        rw [heexp]
        calc
          (2 * pCoeff) ^ 2 * Real.exp (2 * (h + 2)) *
              Real.exp (4 * pCoeff * (h + 2)) =
            (4 * pCoeff ^ 2) *
              (Real.exp (2 * (h + 2)) *
                Real.exp (4 * pCoeff * (h + 2))) := by ring
          _ = (4 * pCoeff ^ 2) *
              Real.exp (2 * (h + 2) + 4 * pCoeff * (h + 2)) := by
            rw [exp_mul_exp]
          _ = _ := by congr 1 <;> ring_nf
  have hMpow : M ^ 2 ≤
      (4 * pCoeff ^ 2) * Real.exp (2 * (h + 2)) / eta ^ 2 := by
    have hright : 0 ≤
        (2 * pCoeff * Real.exp (h + 2)) / eta := by positivity
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ M) hMbound 2
    calc
      M ^ 2 ≤ ((2 * pCoeff * Real.exp (h + 2)) / eta) ^ 2 := hsq
      _ = (4 * pCoeff ^ 2) * Real.exp (2 * (h + 2)) / eta ^ 2 := by
        rw [div_pow, mul_pow, exp_pow_two]
        ring
  have henv : variableLogFreeDensityEnvelope T N J eta ≤
      (16 * pCoeff ^ 4) * envCoeff / eta ^ 2 *
        Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
          4 * pCoeff + 4) * (h + 2)) := by
    unfold variableLogFreeDensityEnvelope
    have h578 :
        (578 : ℝ) ^ (2 * J) ≤
          Real.exp (Real.log ((578 : ℝ) ^ 2) *
            ((a : ℝ) * (h + 2))) := by
      have heq : (578 : ℝ) ^ (2 * J) = ((578 : ℝ) ^ 2) ^ J := by
        simp only [pow_mul]
      rw [heq]
      exact nat_pow_le_exp_of_cast_le (by norm_num) hJbound
    calc
      (578 : ℝ) ^ (2 * J) *
          ((2 * eta * P) * Real.exp (2 * eta * P)) ^ 2 *
            (envCoeff * M ^ 2) ≤
        Real.exp (Real.log ((578 : ℝ) ^ 2) *
            ((a : ℝ) * (h + 2))) *
          ((4 * pCoeff ^ 2) *
            Real.exp ((2 + 4 * pCoeff) * (h + 2))) *
          (envCoeff *
            ((4 * pCoeff ^ 2) * Real.exp (2 * (h + 2)) / eta ^ 2)) := by
        have hAB :
            (578 : ℝ) ^ (2 * J) *
                ((2 * eta * P) * Real.exp (2 * eta * P)) ^ 2 ≤
              Real.exp (Real.log ((578 : ℝ) ^ 2) *
                  ((a : ℝ) * (h + 2))) *
                ((4 * pCoeff ^ 2) *
                  Real.exp ((2 + 4 * pCoeff) * (h + 2))) := by
          exact mul_le_mul h578 hdetector (by positivity) (by positivity)
        have hCpart :
            envCoeff * M ^ 2 ≤
              envCoeff *
                ((4 * pCoeff ^ 2) * Real.exp (2 * (h + 2)) / eta ^ 2) :=
          mul_le_mul_of_nonneg_left hMpow (by positivity)
        exact mul_le_mul hAB hCpart (by positivity) (by positivity)
      _ = (16 * pCoeff ^ 4) * envCoeff / eta ^ 2 *
        Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
          4 * pCoeff + 4) * (h + 2)) := by
        calc
          _ = (16 * pCoeff ^ 4) * envCoeff / eta ^ 2 *
                (Real.exp (Real.log ((578 : ℝ) ^ 2) *
                    ((a : ℝ) * (h + 2))) *
                  Real.exp ((2 + 4 * pCoeff) * (h + 2)) *
                  Real.exp (2 * (h + 2))) :=
            envelope_coefficient_rearrangement pCoeff envCoeff eta _ _ _
          _ = (16 * pCoeff ^ 4) * envCoeff / eta ^ 2 *
                Real.exp
                  (Real.log ((578 : ℝ) ^ 2) * ((a : ℝ) * (h + 2)) +
                    (2 + 4 * pCoeff) * (h + 2) + 2 * (h + 2)) := by
            rw [exp_mul_exp_mul_exp
              (Real.log ((578 : ℝ) ^ 2) * ((a : ℝ) * (h + 2)))
              ((2 + 4 * pCoeff) * (h + 2))
              (2 * (h + 2))]
          _ = _ := by congr 1 <;> ring_nf
  exact ⟨hJ, hJbound, hJexp, hJoneExp, hKlocal, henv⟩

/-- A power-form log-free density estimate, uniform above the Page width.
The constants depend only on the fixed positive lower-width parameter. -/
theorem exists_variable_logFreeDensity_power_bound
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (Q T : ℕ), 2 ≤ Q → 2 ≤ T →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          lambda ≤ eta * Real.log B →
          (primitiveHighZeroMass Q eta T : ℝ) ≤
            C * Real.log B ^ 3 *
              B ^ (c * eta) := by
  obtain ⟨κ, D, A, hκ, hD, hA, hdensity⟩ :=
    exists_variable_logFreeDensity_envelope_parameters
  let E : ℕ := D + κ
  let a : ℕ := (D + κ) * variableDetectorHeightDilation E
  let C₀ : ℝ := Real.log 4 + 4
  let cTail : ℝ := 12 * C₀
  let rCoeff : ℝ := 4 * (Real.log (1 + cTail) + Real.log 4624)
  let pCoeff : ℝ := rCoeff * (a : ℝ) + 1
  let base : ℝ := (578 : ℝ) ^ 2 * 2312
  let kCoeff : ℝ := 32 * C₀ + 256 * (A : ℝ) / 3
  let envCoeff : ℝ := 2 * Real.exp 2 * (1 + 8 * Real.pi)
  let c : ℝ := Real.log base * (a : ℝ) + 4 * pCoeff + 7
  let Craw : ℝ := 256 * kCoeff * ((a : ℝ) + 1) * (a : ℝ) *
    (12 * C₀) * (16 * pCoeff ^ 4) * envCoeff
  let C : ℝ := Craw * Real.exp (2 * c) / lambda ^ 3
  have haNat : 1 ≤ a := by
    dsimp [a, E]
    exact Nat.mul_pos (by omega) (variableDetectorHeightDilation_pos (D + κ))
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast haNat
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hcTail : 0 < cTail := by dsimp [cTail]; positivity
  have hrCoeff : 0 < rCoeff := by
    dsimp [rCoeff]
    have hlogOne : 0 < Real.log (1 + cTail) :=
      Real.log_pos (by linarith)
    have hlogBase : 0 < Real.log (4624 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hpCoeff : 0 < pCoeff := by dsimp [pCoeff]; positivity
  have hbase : 1 < base := by dsimp [base]; norm_num
  have hkCoeff : 0 < kCoeff := by dsimp [kCoeff]; positivity
  have henvCoeff : 0 < envCoeff := by dsimp [envCoeff]; positivity
  have hc : 0 < c := by
    dsimp [c]
    have hlogBase : 0 < Real.log base := Real.log_pos hbase
    positivity
  have hCraw : 0 < Craw := by dsimp [Craw]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro Q T hQ hT eta heta heta8
  dsimp only
  intro hlower
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let h : ℝ := eta * Real.log B
  let H₀ : ℕ := Nat.ceil (1 + h)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let Klocal : ℝ := 32 * C₀ + (256 * (A : ℝ) / 3) * h
  have hB8 : (8 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlogB : 0 < Real.log B :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 8) hB8)
  have hlambdaH : lambda ≤ h := by simpa only [h, B] using hlower
  obtain ⟨hJ, hJbound, hJexp, hJoneExp, hKlocal, henv⟩ :=
    variable_envelope_parameter_bounds hκ hD hQ hT heta heta8
  have hraw := hdensity Q T hQ eta heta heta8
  dsimp only at hraw
  have hraw' : (primitiveHighZeroMass Q eta T : ℝ) ≤
      (Klocal * ((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) /
        ((delta * eta) * (1 / 16 : ℝ) ^ 2) := by
    change (primitiveHighZeroMass Q eta T : ℝ) ≤
      (Klocal * ((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) /
        ((delta * eta) * (1 / 16 : ℝ) ^ 2) at hraw
    exact hraw
  have hdeltaInv : delta⁻¹ =
      12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J := by
    dsimp [delta, variableDetectorPropagationRadius, C₀]
    rw [inv_inv]
  have hrawRewrite :
      (Klocal * ((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) /
        ((delta * eta) * (1 / 16 : ℝ) ^ 2) =
      256 * Klocal * ((J + 1 : ℕ) : ℝ) * (J : ℝ) *
        (12 * C₀) * (2312 : ℝ) ^ J *
          variableLogFreeDensityEnvelope T N J eta / eta := by
    rw [div_eq_mul_inv, mul_inv, mul_inv, hdeltaInv]
    field_simp
    ring
  rw [hrawRewrite] at hraw'
  have hboundBeforeEta :
      (primitiveHighZeroMass Q eta T : ℝ) ≤
        Craw / eta ^ 3 * Real.exp (c * (h + 2)) := by
    calc
      (primitiveHighZeroMass Q eta T : ℝ) ≤
          256 * Klocal * ((J + 1 : ℕ) : ℝ) * (J : ℝ) *
            (12 * C₀) * (2312 : ℝ) ^ J *
              variableLogFreeDensityEnvelope T N J eta / eta := hraw'
      _ ≤ 256 * (kCoeff * Real.exp (h + 2)) *
          (((a : ℝ) + 1) * Real.exp (h + 2)) *
          ((a : ℝ) * Real.exp (h + 2)) *
          (12 * C₀) * (2312 : ℝ) ^ J *
          (((16 * pCoeff ^ 4) * envCoeff / eta ^ 2) *
            Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
              4 * pCoeff + 4) * (h + 2))) / eta := by
        gcongr
        exact variableLogFreeDensityEnvelope_nonneg T N J heta.le
      _ = Craw / eta ^ 3 *
          ((2312 : ℝ) ^ J *
            Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
              4 * pCoeff + 7) * (h + 2))) := by
        calc
          _ = Craw / eta ^ 3 *
              ((2312 : ℝ) ^ J *
                Real.exp (3 * (h + 2) +
                  (Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
                    4 * pCoeff + 4) * (h + 2))) := by
            dsimp [Craw]
            exact density_coefficient_growth_rearrangement
              kCoeff (a : ℝ) C₀ pCoeff envCoeff eta
                ((2312 : ℝ) ^ J) (h + 2)
                ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
                  4 * pCoeff + 4) * (h + 2))
          _ = _ := by congr 2 <;> ring_nf
      _ ≤ Craw / eta ^ 3 *
          (Real.exp (Real.log 2312 * ((a : ℝ) * (h + 2))) *
            Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
              4 * pCoeff + 7) * (h + 2))) := by
        gcongr
        exact nat_pow_le_exp_of_cast_le (by norm_num) hJbound
      _ = Craw / eta ^ 3 *
          Real.exp (c * (h + 2)) := by
        congr 1
        rw [← Real.exp_add]
        have hlogBase : Real.log base =
            Real.log ((578 : ℝ) ^ 2) + Real.log 2312 := by
          dsimp [base]
          rw [Real.log_mul (by norm_num : (578 : ℝ) ^ 2 ≠ 0)
            (by norm_num : (2312 : ℝ) ≠ 0)]
        dsimp only [c]
        rw [hlogBase]
        congr 1
        ring_nf
  have hetaInv : eta⁻¹ ≤ Real.log B / lambda := by
    rw [inv_eq_one_div]
    rw [div_le_div_iff₀ heta hlambda]
    simpa only [h, one_mul, mul_one, mul_comm] using hlambdaH
  have hetaInvCube : eta⁻¹ ^ 3 ≤
      Real.log B ^ 3 / lambda ^ 3 := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ eta⁻¹)
      hetaInv 3
    calc
      eta⁻¹ ^ 3 ≤ (Real.log B / lambda) ^ 3 := hpow
      _ = Real.log B ^ 3 / lambda ^ 3 := by rw [div_pow]
  have hpowB : Real.exp (c * h) = B ^ (c * eta) := by
    dsimp [h]
    rw [Real.rpow_def_of_pos
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) hB8)]
    congr 1
    ring
  calc
    (primitiveHighZeroMass Q eta T : ℝ) ≤
        Craw / eta ^ 3 *
          Real.exp (c * (h + 2)) := hboundBeforeEta
    _ = Craw * eta⁻¹ ^ 3 *
          (Real.exp (2 * c) * Real.exp (c * h)) := by
      rw [show c * (h + 2) = 2 * c + c * h by ring, Real.exp_add]
      field_simp
    _ ≤ Craw * (Real.log B ^ 3 / lambda ^ 3) *
            (Real.exp (2 * c) * Real.exp (c * h)) := by gcongr
    _ = C * Real.log B ^ 3 *
          B ^ (c * eta) := by
      rw [hpowB]
      dsimp [C]
      field_simp

end

end Erdos48
