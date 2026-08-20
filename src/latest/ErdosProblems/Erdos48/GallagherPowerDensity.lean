/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherGammaGrowth
import ErdosProblems.Erdos48.GallagherRawDensity
import ErdosProblems.Erdos48.VariableLogFreeDensityPower

/-!
# Power-form amplified Gallagher zero density

This file removes the detector-order and cutoff parameters from the amplified
Gallagher mean.  Above any fixed Page width it proves a genuine power-form
primitive zero-density estimate, without the logarithmic factor present in the
unamplified large-sieve estimate.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

lemma divide_by_scaled_product
    {X delta h F : ℝ} (hdelta : 0 < delta) (hh : 0 < h)
    (hF : delta⁻¹ = F) :
    X / (delta * h / 512) = 512 * X * F * h⁻¹ := by
  have hdenInv : (delta * h / 512)⁻¹ = 512 * delta⁻¹ * h⁻¹ := by
    field_simp [hdelta.ne', hh.ne']
  rw [div_eq_mul_inv, hdenInv, hF]
  ring

lemma pow_2312_le_exp_of_cast_le
    {u : ℝ} {n : ℕ} (hn : (n : ℝ) ≤ u) :
    (2312 : ℝ) ^ n ≤ Real.exp (Real.log 2312 * u) :=
  nat_pow_le_exp_of_cast_le (a := (2312 : ℝ)) (by norm_num) hn

theorem variableZeroDetectorTailRadius_le_linear
    {J : ℕ} (hJ : 1 ≤ J) :
    variableZeroDetectorTailRadius J ≤
      4 * (Real.log (1 + 12 * (Real.log 4 + 4)) + Real.log 4624) * (J : ℝ) := by
  let C₀ : ℝ := Real.log 4 + 4
  let cTail : ℝ := 12 * C₀
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hcTail : 0 < cTail := by dsimp [cTail]; positivity
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
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  calc
    variableZeroDetectorTailRadius J =
        4 * Real.log (1 + cTail * (4624 : ℝ) ^ J) := by
      simp only [variableZeroDetectorTailRadius, cTail, C₀]
    _ ≤ 4 * Real.log ((1 + cTail) * (4624 : ℝ) ^ J) := by gcongr
    _ = 4 * (Real.log (1 + cTail) +
        (J : ℝ) * Real.log 4624) := by
      rw [Real.log_mul (by positivity) (by positivity), hlogPow]
    _ ≤ 4 * ((Real.log (1 + cTail) + Real.log 4624) * (J : ℝ)) := by
      nlinarith
    _ = _ := by dsimp [cTail, C₀]; ring

theorem gallagherPageEndpointEnvelope_le_exp_growth
    {J : ℕ} {R a h rCoeff : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hr : 0 ≤ rCoeff)
    (hJ : (J : ℝ) ≤ a * (h + 2))
    (hR : R ≤ rCoeff * a * (h + 2)) :
    gallagherPageEndpointEnvelope R J ≤
      2 * Real.exp
        ((Real.log ((578 : ℝ) ^ 2) * a + 4 * rCoeff * a + 1) * (h + 2)) := by
  have hbase : (1 : ℝ) ≤ (578 : ℝ) ^ 2 := by norm_num
  have h578 : (578 : ℝ) ^ (2 * J) ≤
      Real.exp (Real.log ((578 : ℝ) ^ 2) * (a * (h + 2))) := by
    have heq : (578 : ℝ) ^ (2 * J) = ((578 : ℝ) ^ 2) ^ J := by
      simp only [pow_mul]
    rw [heq]
    exact nat_pow_le_exp_of_cast_le hbase hJ
  have hRexp : Real.exp (4 * R + 1) ≤
      Real.exp ((4 * rCoeff * a + 1) * (h + 2)) := by
    rw [Real.exp_le_exp]
    have hhplus : (1 : ℝ) ≤ h + 2 := by linarith
    nlinarith
  unfold gallagherPageEndpointEnvelope
  calc
    2 * (578 : ℝ) ^ (2 * J) * Real.exp (4 * R + 1) ≤
        2 * Real.exp (Real.log ((578 : ℝ) ^ 2) * (a * (h + 2))) *
          Real.exp ((4 * rCoeff * a + 1) * (h + 2)) := by gcongr
    _ = 2 * (Real.exp (Real.log ((578 : ℝ) ^ 2) * (a * (h + 2))) *
          Real.exp ((4 * rCoeff * a + 1) * (h + 2))) := by ring
    _ = 2 * Real.exp
        (Real.log ((578 : ℝ) ^ 2) * (a * (h + 2)) +
          (4 * rCoeff * a + 1) * (h + 2)) := by rw [← Real.exp_add]
    _ = _ := by congr 2 <;> ring_nf

theorem normalizedGallagherDerivativeGammaCoefficient_le_exp_growth
    {eta : ℝ} (heta : 0 ≤ eta) (heta8 : eta ≤ 1 / 8)
    {J k : ℕ} (hkJ : k ≤ J) {a h : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hJ : (J : ℝ) ≤ a * (h + 2))
    (hJone : ((J + 1 : ℕ) : ℝ) ≤ (a + 1) * Real.exp (h + 2)) :
    normalizedGallagherDerivativeGammaCoefficient eta J k ≤
      ((40 / Real.log 2) * (a + 1) ^ 2) *
        Real.exp
          ((Real.log ((578 : ℝ) ^ 2) * a + Real.log 16 * a + 2) * (h + 2)) := by
  have hbase578 : (1 : ℝ) ≤ (578 : ℝ) ^ 2 := by norm_num
  have hbase16 : (1 : ℝ) ≤ 16 := by norm_num
  have h578 : (578 : ℝ) ^ (2 * J) ≤
      Real.exp (Real.log ((578 : ℝ) ^ 2) * (a * (h + 2))) := by
    have heq : (578 : ℝ) ^ (2 * J) = ((578 : ℝ) ^ 2) ^ J := by
      simp only [pow_mul]
    rw [heq]
    exact nat_pow_le_exp_of_cast_le hbase578 hJ
  have h16 : (16 : ℝ) ^ J ≤
      Real.exp (Real.log 16 * (a * (h + 2))) :=
    nat_pow_le_exp_of_cast_le hbase16 hJ
  have hJoneSq : (((J + 1 : ℕ) : ℝ) ^ 2) ≤
      (a + 1) ^ 2 * Real.exp (2 * (h + 2)) := by
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (J + 1 : ℕ)) hJone 2
    calc
      _ ≤ ((a + 1) * Real.exp (h + 2)) ^ 2 := hsq
      _ = (a + 1) ^ 2 * Real.exp (2 * (h + 2)) := by
        rw [mul_pow]
        have hexp : Real.exp (h + 2) ^ 2 = Real.exp (2 * (h + 2)) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        rw [hexp]
  have hraw := normalizedGallagherDerivativeGammaCoefficient_le_growth
    heta heta8 hkJ
  calc
    normalizedGallagherDerivativeGammaCoefficient eta J k ≤
        (40 / Real.log 2) * (578 : ℝ) ^ (2 * J) *
          (16 : ℝ) ^ J * (J + 1 : ℕ) ^ 2 := hraw
    _ ≤ (40 / Real.log 2) *
          Real.exp (Real.log ((578 : ℝ) ^ 2) * (a * (h + 2))) *
          Real.exp (Real.log 16 * (a * (h + 2))) *
          ((a + 1) ^ 2 * Real.exp (2 * (h + 2))) := by gcongr
    _ = ((40 / Real.log 2) * (a + 1) ^ 2) *
          (Real.exp (Real.log ((578 : ℝ) ^ 2) * (a * (h + 2))) *
            Real.exp (Real.log 16 * (a * (h + 2))) *
            Real.exp (2 * (h + 2))) := by ring
    _ = ((40 / Real.log 2) * (a + 1) ^ 2) *
          Real.exp (Real.log ((578 : ℝ) ^ 2) * (a * (h + 2)) +
            Real.log 16 * (a * (h + 2)) + 2 * (h + 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ = _ := by congr 2 <;> ring_nf

theorem gallagherPageTermEnvelope_le_exp_growth
    {eta : ℝ} (heta : 0 ≤ eta) (heta8 : eta ≤ 1 / 8)
    {J k : ℕ} (hkJ : k ≤ J) {R a h rCoeff P0 : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hr : 0 ≤ rCoeff) (hP0 : 0 ≤ P0)
    (hJ : (J : ℝ) ≤ a * (h + 2))
    (hJone : ((J + 1 : ℕ) : ℝ) ≤ (a + 1) * Real.exp (h + 2))
    (hR : R ≤ rCoeff * a * (h + 2)) :
    let uCoeff : ℝ :=
      Real.log ((578 : ℝ) ^ 2) * a + 4 * rCoeff * a + 1
    let gCoeff : ℝ :=
      Real.log ((578 : ℝ) ^ 2) * a + Real.log 16 * a + 2
    let gConst : ℝ := (40 / Real.log 2) * (a + 1) ^ 2
    let cTerm : ℝ := uCoeff + gCoeff + 3
    gallagherPageEndpointEnvelope R J * h ^ 2 +
        2 * normalizedGallagherDerivativeGammaCoefficient eta J k * h ^ 3 * P0 ≤
      (2 + 2 * gConst * P0) * Real.exp (cTerm * (h + 2)) := by
  dsimp only
  let uCoeff : ℝ :=
    Real.log ((578 : ℝ) ^ 2) * a + 4 * rCoeff * a + 1
  let gCoeff : ℝ :=
    Real.log ((578 : ℝ) ^ 2) * a + Real.log 16 * a + 2
  let gConst : ℝ := (40 / Real.log 2) * (a + 1) ^ 2
  let cTerm : ℝ := uCoeff + gCoeff + 3
  have hu : 0 ≤ uCoeff := by
    dsimp [uCoeff]
    have hlog : 0 ≤ Real.log ((578 : ℝ) ^ 2) := Real.log_nonneg (by norm_num)
    positivity
  have hg : 0 ≤ gCoeff := by
    dsimp [gCoeff]
    have hlog1 : 0 ≤ Real.log ((578 : ℝ) ^ 2) := Real.log_nonneg (by norm_num)
    have hlog2 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    positivity
  have hgConst : 0 ≤ gConst := by dsimp [gConst]; positivity
  have hcTerm : 0 ≤ cTerm := by dsimp [cTerm]; positivity
  have hhplus : 0 ≤ h + 2 := by linarith
  have hhexp : h ≤ Real.exp (h + 2) := by
    calc
      h ≤ h + 2 := by linarith
      _ ≤ Real.exp (h + 2) := add_two_le_exp_add_two
  have hh2 : h ^ 2 ≤ Real.exp (2 * (h + 2)) := by
    calc
      h ^ 2 ≤ Real.exp (h + 2) ^ 2 := pow_le_pow_left₀ hh hhexp 2
      _ = Real.exp (2 * (h + 2)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hh3 : h ^ 3 ≤ Real.exp (3 * (h + 2)) := by
    calc
      h ^ 3 ≤ Real.exp (h + 2) ^ 3 := pow_le_pow_left₀ hh hhexp 3
      _ = Real.exp (3 * (h + 2)) := by
        rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hU := gallagherPageEndpointEnvelope_le_exp_growth
    ha hh hr hJ hR
  have hG := normalizedGallagherDerivativeGammaCoefficient_le_exp_growth
    heta heta8 hkJ ha hh hJ hJone
  have hendpoint :
      gallagherPageEndpointEnvelope R J * h ^ 2 ≤
        2 * Real.exp (cTerm * (h + 2)) := by
    calc
      gallagherPageEndpointEnvelope R J * h ^ 2 ≤
          (2 * Real.exp (uCoeff * (h + 2))) *
            Real.exp (2 * (h + 2)) := mul_le_mul hU hh2 (by positivity) (by positivity)
      _ = 2 * Real.exp ((uCoeff + 2) * (h + 2)) := by
        rw [show (2 * Real.exp (uCoeff * (h + 2))) *
            Real.exp (2 * (h + 2)) =
          2 * (Real.exp (uCoeff * (h + 2)) *
            Real.exp (2 * (h + 2))) by ring, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 2 * Real.exp (cTerm * (h + 2)) := by
        gcongr
        · simpa only [cTerm] using
            (show uCoeff + 2 ≤ uCoeff + gCoeff + 3 by linarith [hg])
  have hderivative :
      2 * normalizedGallagherDerivativeGammaCoefficient eta J k * h ^ 3 * P0 ≤
        (2 * gConst * P0) * Real.exp (cTerm * (h + 2)) := by
    calc
      2 * normalizedGallagherDerivativeGammaCoefficient eta J k * h ^ 3 * P0 ≤
          2 * (gConst * Real.exp (gCoeff * (h + 2))) *
            Real.exp (3 * (h + 2)) * P0 := by gcongr
      _ = (2 * gConst * P0) * Real.exp ((gCoeff + 3) * (h + 2)) := by
        rw [show 2 * (gConst * Real.exp (gCoeff * (h + 2))) *
            Real.exp (3 * (h + 2)) * P0 =
          (2 * gConst * P0) *
            (Real.exp (gCoeff * (h + 2)) * Real.exp (3 * (h + 2))) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ (2 * gConst * P0) * Real.exp (cTerm * (h + 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (by linarith [hu]) hhplus)
  calc
    gallagherPageEndpointEnvelope R J * h ^ 2 +
        2 * normalizedGallagherDerivativeGammaCoefficient eta J k * h ^ 3 * P0 ≤
      2 * Real.exp (cTerm * (h + 2)) +
        (2 * gConst * P0) * Real.exp (cTerm * (h + 2)) :=
      add_le_add hendpoint hderivative
    _ = (2 + 2 * gConst * P0) * Real.exp (cTerm * (h + 2)) := by ring

theorem gallagher_density_algebra
    {Z Klocal delta h kCoeff S a termConst cTerm C₀ lambda : ℝ} {J : ℕ}
    (hdelta : 0 < delta) (hh : 0 < h) (hlambda : 0 < lambda)
    (hlower : lambda ≤ h)
    (hraw : Z * (delta * h / 512) ≤
      Klocal * (S * (a + 1) * termConst *
        Real.exp ((cTerm + 1) * (h + 2))))
    (hK : Klocal ≤ kCoeff * Real.exp (h + 2))
    (hJexp : (J : ℝ) ≤ a * Real.exp (h + 2))
    (hJbound : (J : ℝ) ≤ a * (h + 2))
    (hdeltaInv : delta⁻¹ = 12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J)
    (hkCoeff : 0 ≤ kCoeff) (hS : 0 ≤ S) (ha : 0 ≤ a)
    (htermConst : 0 ≤ termConst) (hC₀ : 0 ≤ C₀) :
    Z ≤
      (512 * kCoeff * (S * (a + 1) * termConst) * (12 * C₀ * a) / lambda) *
        Real.exp ((cTerm + 3 + Real.log 2312 * a) * (h + 2)) := by
  have hfactor : 0 < delta * h / 512 := by positivity
  let X : ℝ := S * (a + 1) * termConst *
    Real.exp ((cTerm + 1) * (h + 2))
  have hX : 0 ≤ X := by
    dsimp only [X]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hS (by linarith)) htermConst)
      (Real.exp_pos _).le
  have hdivide : Z ≤ (Klocal * X) / (delta * h / 512) := by
    apply (le_div_iff₀ hfactor).2
    simpa only [X] using hraw
  have hdivideRewrite :
      (Klocal * X) / (delta * h / 512) =
      512 * Klocal * X *
        (12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J) * h⁻¹ := by
    simpa only [mul_assoc] using
      divide_by_scaled_product hdelta hh hdeltaInv (X := Klocal * X)
  rw [hdivideRewrite] at hdivide
  have h2312 : (2312 : ℝ) ^ J ≤
      Real.exp (Real.log 2312 * (a * (h + 2))) :=
    pow_2312_le_exp_of_cast_le hJbound
  have hinvH : h⁻¹ ≤ lambda⁻¹ := inv_anti₀ hlambda hlower
  have hfactorBound :
      12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J ≤
        12 * C₀ * (a * Real.exp (h + 2)) *
          Real.exp (Real.log 2312 * (a * (h + 2))) := by
    have hproduct : (J : ℝ) * (2312 : ℝ) ^ J ≤
        (a * Real.exp (h + 2)) *
          Real.exp (Real.log 2312 * (a * (h + 2))) :=
      mul_le_mul hJexp h2312 (by positivity) (by positivity)
    have hc0 : 0 ≤ 12 * C₀ := mul_nonneg (by norm_num) hC₀
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproduct hc0
  have hmiddle :
      512 * Klocal * X * (12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J) * h⁻¹ ≤
        512 * (kCoeff * Real.exp (h + 2)) * X *
          (12 * C₀ * (a * Real.exp (h + 2)) *
            Real.exp (Real.log 2312 * (a * (h + 2)))) * lambda⁻¹ := by
    calc
      512 * Klocal * X * (12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J) * h⁻¹ ≤
          512 * (kCoeff * Real.exp (h + 2)) * X *
            (12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J) * h⁻¹ := by gcongr
      _ ≤ 512 * (kCoeff * Real.exp (h + 2)) * X *
            (12 * C₀ * (a * Real.exp (h + 2)) *
              Real.exp (Real.log 2312 * (a * (h + 2)))) * h⁻¹ := by gcongr
      _ ≤ 512 * (kCoeff * Real.exp (h + 2)) * X *
            (12 * C₀ * (a * Real.exp (h + 2)) *
              Real.exp (Real.log 2312 * (a * (h + 2)))) * lambda⁻¹ := by gcongr
  calc
    Z ≤ 512 * Klocal * X *
        (12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J) * h⁻¹ := hdivide
    _ ≤ 512 * (kCoeff * Real.exp (h + 2)) * X *
        (12 * C₀ * (a * Real.exp (h + 2)) *
          Real.exp (Real.log 2312 * (a * (h + 2)))) * lambda⁻¹ := hmiddle
    _ = (512 * kCoeff * (S * (a + 1) * termConst) * (12 * C₀ * a) / lambda) *
        Real.exp ((cTerm + 3 + Real.log 2312 * a) * (h + 2)) := by
      have hexp : Real.exp (h + 2) *
          Real.exp ((cTerm + 1) * (h + 2)) *
          Real.exp (h + 2) *
          Real.exp (Real.log 2312 * (a * (h + 2))) =
          Real.exp ((cTerm + 3 + Real.log 2312 * a) * (h + 2)) := by
        calc
          _ = Real.exp ((h + 2) + (cTerm + 1) * (h + 2) +
              (h + 2) + Real.log 2312 * (a * (h + 2))) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          _ = _ := by congr 1 <;> ring_nf
      dsimp [X]
      rw [div_eq_mul_inv]
      calc
        _ = (512 * kCoeff * (S * (a + 1) * termConst) *
              (12 * C₀ * a) * lambda⁻¹) *
            (Real.exp (h + 2) * Real.exp ((cTerm + 1) * (h + 2)) *
              Real.exp (h + 2) *
              Real.exp (Real.log 2312 * (a * (h + 2)))) := by ring
        _ = _ := by rw [hexp]

theorem gallagher_rawDensity_sum_le_exp_envelope
    {lambda : ℝ} (hlambda : 0 < lambda)
    {κ D Q T : ℕ} (hκ : 1 ≤ κ) (hD : 1 ≤ D)
    (hQ : 2 ≤ Q) (hT : 2 ≤ T)
    {eta : ℝ} (heta : 0 < eta) (heta8 : eta ≤ 1 / 8)
    (hlower : lambda ≤ eta * Real.log ((Q : ℝ) * ((T : ℝ) + 2)))
    (hlogAmp : 2 ≤ Real.log (((Q * (T + 2) : ℕ) : ℝ))) :
    let E : ℕ := D + κ
    let a : ℕ := (D + κ) * variableDetectorHeightDilation E
    let C₀ : ℝ := Real.log 4 + 4
    let cTail : ℝ := 12 * C₀
    let rCoeff : ℝ := 4 * (Real.log (1 + cTail) + Real.log 4624)
    let P0 : ℝ := rCoeff * (a : ℝ) * (1 + 2 / lambda) + 2
    let P : ℝ := 2 * P0
    let S : ℝ := gallagherPageMeanEnvelope P
    let uCoeff : ℝ :=
      Real.log ((578 : ℝ) ^ 2) * (a : ℝ) + 4 * rCoeff * (a : ℝ) + 1
    let gCoeff : ℝ :=
      Real.log ((578 : ℝ) ^ 2) * (a : ℝ) + Real.log 16 * (a : ℝ) + 2
    let gConst : ℝ := (40 / Real.log 2) * ((a : ℝ) + 1) ^ 2
    let cTerm : ℝ := uCoeff + gCoeff + 3
    let termConst : ℝ := 2 + 2 * gConst * P0
    let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
    let Amp : ℕ := Q * (T + 2)
    let h : ℝ := eta * Real.log B
    let H₀ : ℕ := Nat.ceil (1 + h)
    let H : ℕ := variableDetectorHeightDilation E * H₀
    let J : ℕ := (D + κ) * H
    let R : ℝ := variableZeroDetectorTailRadius J
    let N : ℕ := zeroDetectorCutoff R eta
    let L : ℕ := D * H + 1
    (∑ j ∈ Finset.Icc L J,
      gallagherRawDensityTermAt Q (T + 1) E N J j
        (Real.log Amp / 2) eta R) ≤
      S * ((a : ℝ) + 1) * termConst *
        Real.exp ((cTerm + 1) * (h + 2)) := by
  dsimp only
  let E : ℕ := D + κ
  let a : ℕ := (D + κ) * variableDetectorHeightDilation E
  let C₀ : ℝ := Real.log 4 + 4
  let cTail : ℝ := 12 * C₀
  let rCoeff : ℝ := 4 * (Real.log (1 + cTail) + Real.log 4624)
  let P0 : ℝ := rCoeff * (a : ℝ) * (1 + 2 / lambda) + 2
  let P : ℝ := 2 * P0
  let S : ℝ := gallagherPageMeanEnvelope P
  let uCoeff : ℝ :=
    Real.log ((578 : ℝ) ^ 2) * (a : ℝ) + 4 * rCoeff * (a : ℝ) + 1
  let gCoeff : ℝ :=
    Real.log ((578 : ℝ) ^ 2) * (a : ℝ) + Real.log 16 * (a : ℝ) + 2
  let gConst : ℝ := (40 / Real.log 2) * ((a : ℝ) + 1) ^ 2
  let cTerm : ℝ := uCoeff + gCoeff + 3
  let termConst : ℝ := 2 + 2 * gConst * P0
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let Amp : ℕ := Q * (T + 2)
  let h : ℝ := eta * Real.log B
  let H₀ : ℕ := Nat.ceil (1 + h)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  have haNat : 1 ≤ a := by
    dsimp [a, E]
    exact Nat.mul_pos (by omega) (variableDetectorHeightDilation_pos (D + κ))
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast haNat
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hcTail : 0 < cTail := by dsimp [cTail]; positivity
  have hrCoeff : 0 < rCoeff := by
    dsimp [rCoeff]
    have hlogOne : 0 < Real.log (1 + cTail) := Real.log_pos (by linarith)
    have hlogBase : 0 < Real.log (4624 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hP0 : 0 < P0 := by
    dsimp [P0]
    have hscale : 0 < 1 + 2 / lambda := by positivity
    positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hS : 0 < S := by
    dsimp [S]
    unfold gallagherPageMeanEnvelope
    positivity
  have htermConst : 0 < termConst := by
    dsimp [termConst, gConst]
    positivity
  have hbCast : (Amp : ℝ) = B := by
    dsimp [Amp, B]
    push_cast
    ring
  have hB8 : (8 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlogB : 0 < Real.log B :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 8) hB8)
  have hlogBone : (1 : ℝ) ≤ Real.log B := by
    rw [← hbCast]
    linarith
  have hh : 0 < h := by
    dsimp [h]
    exact hlambda.trans_le hlower
  have hlambdaH : lambda ≤ h := by simpa only [h, B] using hlower
  obtain ⟨hJ, hJbound, _hJexp, hJoneExp, _hKlocal, _henv⟩ :=
    variable_envelope_parameter_bounds (κ := κ) (D := D) (A := 37)
      (Q := Q) (T := T) hκ hD hQ hT heta heta8
  have hRlinear : R ≤ rCoeff * (J : ℝ) := by
    simpa only [R, rCoeff, cTail, C₀, mul_assoc] using
      variableZeroDetectorTailRadius_le_linear hJ
  have hRbound : R ≤ rCoeff * (a : ℝ) * (h + 2) := by
    calc
      R ≤ rCoeff * (J : ℝ) := hRlinear
      _ ≤ rCoeff * ((a : ℝ) * (h + 2)) := by gcongr
      _ = _ := by ring
  have hscale : h + 2 ≤ (1 + 2 / lambda) * h := by
    have htwo : (2 : ℝ) ≤ 2 * h / lambda := by
      apply (le_div_iff₀ hlambda).2
      nlinarith
    calc
      h + 2 ≤ h + 2 * h / lambda := by
        simpa only [add_comm] using add_le_add_left htwo h
      _ = (1 + 2 / lambda) * h := by ring
  have hRscaled : R ≤
      (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * h := by
    calc
      R ≤ rCoeff * (a : ℝ) * (h + 2) := hRbound
      _ ≤ rCoeff * (a : ℝ) * ((1 + 2 / lambda) * h) := by gcongr
      _ = _ := by ring
  have hRover : R / eta + 2 ≤ P0 * Real.log Amp := by
    rw [show Real.log (Amp : ℝ) = Real.log B by rw [hbCast]]
    have htwoLog : (2 : ℝ) ≤ 2 * Real.log B := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlogBone (show (0 : ℝ) ≤ 2 by norm_num)
    have hRdiv : R / eta ≤
        (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * Real.log B := by
      apply (div_le_iff₀ heta).2
      calc
        R ≤ (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * h := hRscaled
        _ = (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * Real.log B * eta := by
          dsimp [h]
          ring
    calc
      R / eta + 2 ≤
          (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * Real.log B + 2 := by
        simpa only [add_comm] using add_le_add_right hRdiv 2
      _ ≤ (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * Real.log B +
          2 * Real.log B := by
        simpa only [add_comm] using
          add_le_add_left htwoLog
            ((rCoeff * (a : ℝ) * (1 + 2 / lambda)) * Real.log B)
      _ = P0 * Real.log B := by
        change _ = (rCoeff * (a : ℝ) * (1 + 2 / lambda) + 2) * Real.log B
        ring
  have hNlength :
      (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) ≤ P * Real.log Amp := by
    have hdyadic := variableDetectorDyadicLength_zeroDetectorCutoff_le
      (show 0 ≤ R by dsimp [R]; exact variableZeroDetectorTailRadius_pos J |>.le) heta
    have hdyadic' :
        (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) * Real.log 2 ≤
          R / eta + 2 := by
      simpa only [N, variableDetectorDyadicLength] using hdyadic
    have hprod := hdyadic'.trans hRover
    have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 :=
      lt_trans (by norm_num) Real.log_two_gt_d9
    have hM0 : 0 ≤ (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) := by positivity
    have hhalf : (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) / 2 ≤
        (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) * Real.log 2 := by
      have hm := mul_le_mul_of_nonneg_left hlogTwoHalf.le hM0
      simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using hm
    have hhalfprod := hhalf.trans hprod
    calc
      (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) =
          2 * ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) / 2) := by ring
      _ ≤ 2 * (P0 * Real.log Amp) :=
        mul_le_mul_of_nonneg_left hhalfprod (by norm_num)
      _ = P * Real.log Amp := by dsimp [P]; ring
  have hharm : ∀ j ∈ Finset.Icc L J,
      (∑ m ∈ Finset.Icc (variableDetectorLowerCutoff E eta j) N,
        (m : ℝ)⁻¹) ≤ P0 * Real.log Amp := by
    intro j hj
    have hjLower : D * H + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hB : (1 : ℝ) ≤ B := by linarith
    have hYcompare : zeroDetectorLowerCutoff B ≤
        variableDetectorLowerCutoff E eta j :=
      zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
        hD hB heta (by exact le_rfl) (by exact le_rfl) hjLower
    have hY1 : 1 ≤ variableDetectorLowerCutoff E eta j := by
      have hzero : 1 ≤ zeroDetectorLowerCutoff B := by
        unfold zeroDetectorLowerCutoff
        exact Nat.one_le_pow (zeroDetectorLowerLog B) 2 (by omega)
      exact hzero.trans hYcompare
    have hsum := sum_Icc_inv_le_one_add_log (N := N) hY1
    have hlogN := log_zeroDetectorCutoff_le
      (show 0 ≤ R by dsimp [R]; exact variableZeroDetectorTailRadius_pos J |>.le) heta
    calc
      _ ≤ 1 + Real.log N := hsum
      _ ≤ R / eta + 2 := by linarith
      _ ≤ P0 * Real.log Amp := hRover
  have hAmp2 : 2 ≤ Amp := by
    dsimp [Amp]
    calc
      2 ≤ Q := hQ
      _ = Q * 1 := by omega
      _ ≤ Q * (T + 2) := Nat.mul_le_mul_left Q (by omega)
  have hpow : ∀ j ∈ Finset.Icc L J,
      Amp ^ 4 ≤ variableDetectorLowerCutoff E eta j := by
    intro j hj
    have hjLower : D * H + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hB : (1 : ℝ) ≤ B := by linarith
    have hcompare : zeroDetectorLowerCutoff B ≤
        variableDetectorLowerCutoff E eta j :=
      zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
        hD hB heta (by exact le_rfl) (by exact le_rfl) hjLower
    have hbpow : Amp ^ 4 ≤ zeroDetectorLowerCutoff B := by
      rw [← hbCast]
      exact pow_four_le_zeroDetectorLowerCutoff Amp hAmp2
    exact hbpow.trans hcompare
  have hetaEq : eta = h / Real.log Amp := by
    rw [show Real.log (Amp : ℝ) = Real.log B by rw [hbCast]]
    dsimp [h]
    field_simp
  have hterm : ∀ j ∈ Finset.Icc L J,
      gallagherRawDensityTermAt Q (T + 1) E N J j
          (Real.log Amp / 2) eta R ≤
        S * (2 + 2 * gConst * P0) * Real.exp (cTerm * (h + 2)) := by
    intro j hj
    have hjOne : 1 ≤ j := by
      have := (Finset.mem_Icc.mp hj).1
      dsimp [L] at this
      omega
    have hjJ : j - 1 ≤ J := by
      have := (Finset.mem_Icc.mp hj).2
      omega
    have hpage := gallagherRawDensityTermAt_le_page
      (b := Amp) (Q := Q) (T := T + 1) (E := E) (J := J) (j := j)
      (lambda := h) (eta := eta) (R := R) (P := P) (H := P0)
      hAmp2 hh heta heta8 hetaEq
      (show 0 ≤ R by dsimp [R]; exact variableZeroDetectorTailRadius_pos J |>.le)
      hjOne (hpow j hj) hP.le hP0.le hNlength (hharm j hj)
    have henv := gallagherPageTermEnvelope_le_exp_growth
      (eta := (1 / 8 : ℝ)) (by norm_num) (by norm_num) hjJ
      (zero_le_one.trans ha) hh.le hrCoeff.le hP0.le
      hJbound hJoneExp hRbound
    calc
      gallagherRawDensityTermAt Q (T + 1) E N J j
          (Real.log Amp / 2) eta R ≤
        S * (gallagherPageEndpointEnvelope R J * h ^ 2 +
          2 * normalizedGallagherDerivativeGammaCoefficient (1 / 8) J
            (j - 1) * h ^ 3 * P0) := hpage
      _ ≤ S * ((2 + 2 * gConst * P0) *
          Real.exp (cTerm * (h + 2))) :=
        mul_le_mul_of_nonneg_left henv hS.le
      _ = _ := by ring
  let V : ℝ := S * (2 + 2 * gConst * P0) * Real.exp (cTerm * (h + 2))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  calc
    _ ≤ ∑ _j ∈ Finset.Icc L J, V := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [V] using hterm j hj
    _ = ((Finset.Icc L J).card : ℝ) * V := by simp
    _ ≤ (((J + 1 : ℕ) : ℝ)) * V := by
      apply mul_le_mul_of_nonneg_right _ hV
      exact_mod_cast (show (Finset.Icc L J).card ≤ J + 1 by
        rw [Nat.card_Icc]
        omega)
    _ ≤ (((a : ℝ) + 1) * Real.exp (h + 2)) * V := by gcongr
    _ = S * ((a : ℝ) + 1) * termConst *
        Real.exp ((cTerm + 1) * (h + 2)) := by
      dsimp [V, termConst]
      calc
        ((a : ℝ) + 1) * Real.exp (h + 2) *
            (S * (2 + 2 * gConst * P0) * Real.exp (cTerm * (h + 2))) =
          S * ((a : ℝ) + 1) * (2 + 2 * gConst * P0) *
            (Real.exp (h + 2) * Real.exp (cTerm * (h + 2))) := by ring
        _ = S * ((a : ℝ) + 1) * (2 + 2 * gConst * P0) *
            Real.exp ((h + 2) + cTerm * (h + 2)) := by rw [← Real.exp_add]
        _ = _ := by congr 2 <;> ring_nf

/-- Amplified Gallagher density in power form, uniform above a fixed Page
width.  Unlike the unamplified estimate, there is no residual logarithmic
factor. -/
theorem exists_gallagher_logFreeDensity_power_bound
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ K Camp C c : ℝ, 0 < K ∧ 0 < C ∧ 0 < c ∧
      ∀ (Q T : ℕ), 2 ≤ Q → 2 ≤ T →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          lambda ≤ eta * Real.log B →
          let Amp := Q * (T + 2)
          2 ≤ Real.log Amp →
          20 * (K + (Real.log (Real.log Amp) + Camp + 2) + Real.log 2) ≤
            Real.log Amp →
          (primitiveHighZeroMass Q eta T : ℝ) ≤ C * B ^ (c * eta) := by
  obtain ⟨κ, D, A, K, Camp, hκ, hD, hA, hK, hraw⟩ :=
    exists_gallagher_rawDensity_globalProduct_parameters
  let E : ℕ := D + κ
  let a : ℕ := (D + κ) * variableDetectorHeightDilation E
  let C₀ : ℝ := Real.log 4 + 4
  let cTail : ℝ := 12 * C₀
  let rCoeff : ℝ := 4 * (Real.log (1 + cTail) + Real.log 4624)
  let kCoeff : ℝ := 32 * C₀ + 256 * (A : ℝ) / 3
  let P0 : ℝ := rCoeff * (a : ℝ) * (1 + 2 / lambda) + 2
  let P : ℝ := 2 * P0
  let S : ℝ := gallagherPageMeanEnvelope P
  let uCoeff : ℝ :=
    Real.log ((578 : ℝ) ^ 2) * (a : ℝ) + 4 * rCoeff * (a : ℝ) + 1
  let gCoeff : ℝ :=
    Real.log ((578 : ℝ) ^ 2) * (a : ℝ) + Real.log 16 * (a : ℝ) + 2
  let gConst : ℝ := (40 / Real.log 2) * ((a : ℝ) + 1) ^ 2
  let cTerm : ℝ := uCoeff + gCoeff + 3
  let termConst : ℝ := 2 + 2 * gConst * P0
  let c : ℝ := cTerm + 3 + Real.log 2312 * (a : ℝ)
  let Craw : ℝ :=
    512 * kCoeff * (S * ((a : ℝ) + 1) * termConst) *
      (12 * C₀ * (a : ℝ)) / lambda
  let C : ℝ := Craw * Real.exp (2 * c)
  have haNat : 1 ≤ a := by
    dsimp [a, E]
    exact Nat.mul_pos (by omega) (variableDetectorHeightDilation_pos (D + κ))
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast haNat
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hcTail : 0 < cTail := by dsimp [cTail]; positivity
  have hrCoeff : 0 < rCoeff := by
    dsimp [rCoeff]
    have hlogOne : 0 < Real.log (1 + cTail) := Real.log_pos (by linarith)
    have hlogBase : 0 < Real.log (4624 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hkCoeff : 0 < kCoeff := by dsimp [kCoeff]; positivity
  have hP0 : 0 < P0 := by
    dsimp [P0]
    have hscale : 0 < 1 + 2 / lambda := by positivity
    positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hS : 0 < S := by
    dsimp [S]
    unfold gallagherPageMeanEnvelope
    positivity
  have hgConst : 0 < gConst := by dsimp [gConst]; positivity
  have huCoeff : 0 < uCoeff := by
    dsimp [uCoeff]
    have hlog : 0 ≤ Real.log ((578 : ℝ) ^ 2) := Real.log_nonneg (by norm_num)
    positivity
  have hgCoeff : 0 < gCoeff := by
    dsimp [gCoeff]
    have hlog1 : 0 ≤ Real.log ((578 : ℝ) ^ 2) := Real.log_nonneg (by norm_num)
    have hlog2 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    positivity
  have hcTerm : 0 < cTerm := by dsimp [cTerm]; positivity
  have htermConst : 0 < termConst := by dsimp [termConst]; positivity
  have hc : 0 < c := by
    dsimp [c]
    have hlog : 0 < Real.log (2312 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hCraw : 0 < Craw := by dsimp [Craw]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨K, Camp, C, c, hK, hC, hc, ?_⟩
  intro Q T hQ hT eta heta heta8
  dsimp only
  intro hlower hlogAmp hamp
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let Amp : ℕ := Q * (T + 2)
  let h : ℝ := eta * Real.log B
  let H₀ : ℕ := Nat.ceil (1 + h)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  let Klocal : ℝ := 32 * C₀ + (256 * (A : ℝ) / 3) * h
  have hbCast : (Amp : ℝ) = B := by
    dsimp [Amp, B]
    push_cast
    ring
  have hB8 : (8 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlogB : 0 < Real.log B :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 8) hB8)
  have hlogBone : (1 : ℝ) ≤ Real.log B := by
    rw [← hbCast]
    linarith
  have hh : 0 < h := by
    dsimp [h]
    exact hlambda.trans_le hlower
  have hlambdaH : lambda ≤ h := by simpa only [h, B] using hlower
  obtain ⟨hJ, hJbound, hJexp, hJoneExp, hKlocal, _henv⟩ :=
    variable_envelope_parameter_bounds (κ := κ) (D := D) (A := A)
      (Q := Q) (T := T) hκ hD hQ hT heta heta8
/-
  This is the inlined proof of `gallagher_rawDensity_sum_le_exp_envelope`.
  It is retained temporarily while the extracted declaration is checked.
  have hRlinear : R ≤ rCoeff * (J : ℝ) := by
    simpa only [R, rCoeff, cTail, C₀, mul_assoc] using
      variableZeroDetectorTailRadius_le_linear hJ
  have hRbound : R ≤ rCoeff * (a : ℝ) * (h + 2) := by
    calc
      R ≤ rCoeff * (J : ℝ) := hRlinear
      _ ≤ rCoeff * ((a : ℝ) * (h + 2)) := by gcongr
      _ = _ := by ring
  have hscale : h + 2 ≤ (1 + 2 / lambda) * h := by
    have htwo : (2 : ℝ) ≤ 2 * h / lambda := by
      apply (le_div_iff₀ hlambda).2
      nlinarith
    calc
      h + 2 ≤ h + 2 * h / lambda := by
        simpa only [add_comm] using add_le_add_left htwo h
      _ = (1 + 2 / lambda) * h := by ring
  have hRscaled : R ≤
      (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * h := by
    calc
      R ≤ rCoeff * (a : ℝ) * (h + 2) := hRbound
      _ ≤ rCoeff * (a : ℝ) * ((1 + 2 / lambda) * h) := by gcongr
      _ = _ := by ring
  have hetaLeH : eta ≤ h := by
    simpa only [h, mul_one] using mul_le_mul_of_nonneg_left hlogBone heta.le
  have hRover : R / eta + 2 ≤ P0 * Real.log Amp := by
    rw [show Real.log (Amp : ℝ) = Real.log B by rw [hbCast]]
    have htwoLog : (2 : ℝ) ≤ 2 * Real.log B := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlogBone (show (0 : ℝ) ≤ 2 by norm_num)
    have hRdiv : R / eta ≤
        (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * Real.log B := by
      apply (div_le_iff₀ heta).2
      calc
        R ≤ (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * h := hRscaled
        _ = (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * Real.log B * eta := by
          dsimp [h]
          ring
    calc
      R / eta + 2 ≤
          (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * Real.log B + 2 :=
        by simpa only [add_comm] using add_le_add_right hRdiv 2
      _ ≤ (rCoeff * (a : ℝ) * (1 + 2 / lambda)) * Real.log B +
          2 * Real.log B := by
        simpa only [add_comm] using
          add_le_add_left htwoLog
            ((rCoeff * (a : ℝ) * (1 + 2 / lambda)) * Real.log B)
      _ = P0 * Real.log B := by
        change _ = (rCoeff * (a : ℝ) * (1 + 2 / lambda) + 2) * Real.log B
        ring
  have hNlength :
      (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) ≤ P * Real.log Amp := by
    have hdyadic := variableDetectorDyadicLength_zeroDetectorCutoff_le
      (show 0 ≤ R by dsimp [R]; exact variableZeroDetectorTailRadius_pos J |>.le) heta
    have hdyadic' :
        (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) * Real.log 2 ≤
          R / eta + 2 := by
      simpa only [N, variableDetectorDyadicLength] using hdyadic
    have hprod := hdyadic'.trans hRover
    have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 :=
      lt_trans (by norm_num) Real.log_two_gt_d9
    have hM0 : 0 ≤ (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) := by positivity
    have hhalf : (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) / 2 ≤
        (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) * Real.log 2 := by
      have hm := mul_le_mul_of_nonneg_left hlogTwoHalf.le hM0
      simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using hm
    have hhalfprod := hhalf.trans hprod
    calc
      (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) =
          2 * ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) / 2) := by ring
      _ ≤ 2 * (P0 * Real.log Amp) :=
        mul_le_mul_of_nonneg_left hhalfprod (by norm_num)
      _ = P * Real.log Amp := by dsimp [P]; ring
  have hharm : ∀ j ∈ Finset.Icc L J,
      (∑ m ∈ Finset.Icc (variableDetectorLowerCutoff E eta j) N,
        (m : ℝ)⁻¹) ≤ P0 * Real.log Amp := by
    intro j hj
    have hjLower : D * H + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hB : (1 : ℝ) ≤ B := by linarith
    have hYcompare : zeroDetectorLowerCutoff B ≤
        variableDetectorLowerCutoff E eta j :=
      zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
        hD hB heta (by exact le_rfl) (by exact le_rfl) hjLower
    have hY1 : 1 ≤ variableDetectorLowerCutoff E eta j := by
      have hzero : 1 ≤ zeroDetectorLowerCutoff B := by
        unfold zeroDetectorLowerCutoff
        exact Nat.one_le_pow (zeroDetectorLowerLog B) 2 (by omega)
      exact hzero.trans hYcompare
    have hsum := sum_Icc_inv_le_one_add_log (N := N) hY1
    have hlogN := log_zeroDetectorCutoff_le
      (show 0 ≤ R by dsimp [R]; exact variableZeroDetectorTailRadius_pos J |>.le) heta
    calc
      _ ≤ 1 + Real.log N := hsum
      _ ≤ R / eta + 2 := by linarith
      _ ≤ P0 * Real.log Amp := hRover
  have hAmp2 : 2 ≤ Amp := by
    dsimp [Amp]
    calc
      2 ≤ Q := hQ
      _ = Q * 1 := by omega
      _ ≤ Q * (T + 2) := Nat.mul_le_mul_left Q (by omega)
  have hpow : ∀ j ∈ Finset.Icc L J,
      Amp ^ 4 ≤ variableDetectorLowerCutoff E eta j := by
    intro j hj
    have hjLower : D * H + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hB : (1 : ℝ) ≤ B := by linarith
    have hcompare : zeroDetectorLowerCutoff B ≤
        variableDetectorLowerCutoff E eta j :=
      zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
        hD hB heta (by exact le_rfl) (by exact le_rfl) hjLower
    have hbpow : Amp ^ 4 ≤ zeroDetectorLowerCutoff B := by
      rw [← hbCast]
      exact pow_four_le_zeroDetectorLowerCutoff Amp hAmp2
    exact hbpow.trans hcompare
  have hetaEq : eta = h / Real.log Amp := by
    rw [show Real.log (Amp : ℝ) = Real.log B by rw [hbCast]]
    dsimp [h]
    field_simp
  have hterm : ∀ j ∈ Finset.Icc L J,
      gallagherRawDensityTermAt Q (T + 1) E N J j
          (Real.log Amp / 2) eta R ≤
        S * (2 + 2 * gConst * P0) * Real.exp (cTerm * (h + 2)) := by
    intro j hj
    have hjOne : 1 ≤ j := by
      have := (Finset.mem_Icc.mp hj).1
      dsimp [L] at this
      omega
    have hjJ : j - 1 ≤ J := by
      have := (Finset.mem_Icc.mp hj).2
      omega
    have hpage := gallagherRawDensityTermAt_le_page
      (b := Amp) (Q := Q) (T := T + 1) (E := E) (J := J) (j := j)
      (lambda := h) (eta := eta) (R := R) (P := P) (H := P0)
      hAmp2 hh heta heta8 hetaEq
      (show 0 ≤ R by dsimp [R]; exact variableZeroDetectorTailRadius_pos J |>.le)
      hjOne (hpow j hj) hP.le hP0.le hNlength (hharm j hj)
    have henv := gallagherPageTermEnvelope_le_exp_growth
      (eta := (1 / 8 : ℝ)) (by norm_num) (by norm_num) hjJ
      (zero_le_one.trans ha) hh.le
      hrCoeff.le hP0.le hJbound hJoneExp hRbound
    calc
      gallagherRawDensityTermAt Q (T + 1) E N J j
          (Real.log Amp / 2) eta R ≤
        S * (gallagherPageEndpointEnvelope R J * h ^ 2 +
          2 * normalizedGallagherDerivativeGammaCoefficient (1 / 8) J
            (j - 1) * h ^ 3 * P0) := hpage
      _ ≤ S * ((2 + 2 * gConst * P0) *
          Real.exp (cTerm * (h + 2))) :=
        mul_le_mul_of_nonneg_left henv hS.le
      _ = _ := by ring
  have hsum :
      (∑ j ∈ Finset.Icc L J,
        gallagherRawDensityTermAt Q (T + 1) E N J j
          (Real.log Amp / 2) eta R) ≤
        S * ((a : ℝ) + 1) * termConst *
          Real.exp ((cTerm + 1) * (h + 2)) := by
    let V : ℝ := S * (2 + 2 * gConst * P0) * Real.exp (cTerm * (h + 2))
    have hV : 0 ≤ V := by dsimp [V]; positivity
    calc
      _ ≤ ∑ _j ∈ Finset.Icc L J, V := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [V] using hterm j hj
      _ = ((Finset.Icc L J).card : ℝ) * V := by simp
      _ ≤ (((J + 1 : ℕ) : ℝ)) * V := by
        apply mul_le_mul_of_nonneg_right _ hV
        exact_mod_cast (show (Finset.Icc L J).card ≤ J + 1 by
          rw [Nat.card_Icc]
          omega)
      _ ≤ (((a : ℝ) + 1) * Real.exp (h + 2)) * V := by gcongr
      _ = S * ((a : ℝ) + 1) * termConst *
          Real.exp ((cTerm + 1) * (h + 2)) := by
        dsimp [V, termConst]
        calc
          ((a : ℝ) + 1) * Real.exp (h + 2) *
              (S * (2 + 2 * gConst * P0) * Real.exp (cTerm * (h + 2))) =
            S * ((a : ℝ) + 1) * (2 + 2 * gConst * P0) *
              (Real.exp (h + 2) * Real.exp (cTerm * (h + 2))) := by ring
          _ = S * ((a : ℝ) + 1) * (2 + 2 * gConst * P0) *
              Real.exp ((h + 2) + cTerm * (h + 2)) := by rw [← Real.exp_add]
          _ = _ := by congr 2 <;> ring_nf
-/
  have hsum :
      (∑ j ∈ Finset.Icc L J,
        gallagherRawDensityTermAt Q (T + 1) E N J j
          (Real.log Amp / 2) eta R) ≤
        S * ((a : ℝ) + 1) * termConst *
          Real.exp ((cTerm + 1) * (h + 2)) := by
    simpa only [E, a, C₀, cTail, rCoeff, P0, P, S, uCoeff, gCoeff,
      gConst, cTerm, termConst, B, Amp, h, H₀, H, J, R, N, L] using
      gallagher_rawDensity_sum_le_exp_envelope hlambda hκ hD hQ hT
        heta heta8 hlower hlogAmp
  have hbase := hraw Q T hQ eta heta heta8
  dsimp only at hbase
  have hraw' : (Real.log Amp / 2) *
      ((primitiveHighZeroMass Q eta T : ℝ) * (delta * eta) *
        (1 / 16 : ℝ) ^ 2) ≤ Klocal *
        (S * ((a : ℝ) + 1) * termConst *
          Real.exp ((cTerm + 1) * (h + 2))) := by
    have h0 := hbase hlogAmp hamp
    have h1 : (Real.log Amp / 2) *
        ((primitiveHighZeroMass Q eta T : ℝ) * (delta * eta) *
          (1 / 16 : ℝ) ^ 2) ≤
        Klocal *
          ∑ j ∈ Finset.Icc L J,
            gallagherRawDensityTermAt Q (T + 1) E N J j
              (Real.log Amp / 2) eta R := by
      simpa only [E, B, Amp, h, H₀, H, J, delta, R, N, L, Klocal] using h0
    exact h1.trans (mul_le_mul_of_nonneg_left hsum (by dsimp [Klocal]; positivity))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact variableDetectorPropagationRadius_pos hJ
  have hleft : (Real.log Amp / 2) *
      ((primitiveHighZeroMass Q eta T : ℝ) * (delta * eta) *
        (1 / 16 : ℝ) ^ 2) =
      (primitiveHighZeroMass Q eta T : ℝ) * (delta * h / 512) := by
    rw [show Real.log (Amp : ℝ) = Real.log B by rw [hbCast]]
    dsimp [h]
    ring
  rw [hleft] at hraw'
  have hdeltaInv : delta⁻¹ = 12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J := by
    dsimp [delta, variableDetectorPropagationRadius, C₀]
    rw [inv_inv]
  have hKbound : Klocal ≤ kCoeff * Real.exp (h + 2) := by
    simpa only [Klocal, kCoeff, C₀, h, a] using hKlocal
  have hbefore : (primitiveHighZeroMass Q eta T : ℝ) ≤
      Craw * Real.exp (c * (h + 2)) := by
    simpa only [Craw, c] using
      gallagher_density_algebra hdelta hh hlambda hlambdaH hraw' hKbound
        hJexp hJbound hdeltaInv hkCoeff.le hS.le (zero_le_one.trans ha)
        htermConst.le hC₀.le
  have hpowB : Real.exp (c * h) = B ^ (c * eta) := by
    dsimp [h]
    rw [Real.rpow_def_of_pos
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) hB8)]
    congr 1
    ring
  calc
    (primitiveHighZeroMass Q eta T : ℝ) ≤
        Craw * Real.exp (c * (h + 2)) := hbefore
    _ = Craw * (Real.exp (2 * c) * Real.exp (c * h)) := by
      rw [show c * (h + 2) = 2 * c + c * h by ring, Real.exp_add]
    _ = C * B ^ (c * eta) := by
      rw [hpowB]
      dsimp only [C]
      ac_rfl

end

end Erdos48
