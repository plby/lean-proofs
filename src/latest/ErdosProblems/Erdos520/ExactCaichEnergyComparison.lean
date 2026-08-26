import ErdosProblems.Erdos520.ExactEnergySmall

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Comparison of the exact and Caich energy normalizations

The exact martingale energy is `H / Z(y)`, where `Z(y)` is the finite Euler
product `primeEnergyNormalizer y`.  Caich's Parseval-side energy is

`2π * damping * H / log y`.

Consequently the two normalizations are comparable as soon as the relevant
upper or lower Mertens product inequality is supplied.  Those deterministic
inequalities remain explicit arguments in this file.
-/

/-- Caich's damping factor is at most one once the current cutoff is no
smaller than the initial cutoff. -/
theorem caich_damping_le_one
    {ell K y₀ y : ℕ} (hy₀ : 1 < y₀) (hy₀y : y₀ ≤ y) :
    Real.exp
        (-Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
          ((ell : ℝ) ^ K)) ≤ 1 := by
  have hlogy₀ : 0 < Real.log (y₀ : ℝ) :=
    Real.log_pos (by exact_mod_cast hy₀)
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le (lt_trans Nat.zero_lt_one hy₀) hy₀y)
  have hlogmono : Real.log (y₀ : ℝ) ≤ Real.log (y : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (lt_trans Nat.zero_lt_one hy₀)
    · exact_mod_cast hy₀y
  have hratio : 1 ≤ Real.log (y : ℝ) / Real.log (y₀ : ℝ) :=
    (one_le_div hlogy₀).2 hlogmono
  apply Real.exp_le_one_iff.2
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Real.log_nonneg hratio))
    (pow_nonneg (Nat.cast_nonneg ell) K)

/-- An upper Mertens-product inequality converts exact martingale energy into
an upper bound for Caich's damped energy. -/
theorem caichNormalizedEnergy_le_mul_exactNormalizedEnergy
    {ell K y₀ y : ℕ} (hy₀ : 1 < y₀) (hy₀y : y₀ ≤ y)
    {C : ℝ}
    (hZupper : primeEnergyNormalizer y ≤ C * Real.log (y : ℝ))
    (omega : Omega) :
    caichNormalizedEnergy ell K y₀ y omega ≤
      (2 * Real.pi * C) * exactNormalizedEnergy omega y := by
  have hy : 1 < y := lt_of_lt_of_le hy₀ hy₀y
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have hZpos : 0 < primeEnergyNormalizer y := primeEnergyNormalizer_pos y
  have hH : 0 ≤ smoothEnergy omega y := smoothEnergy_nonneg omega y
  have hdamp :
      Real.exp
          (-Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
            ((ell : ℝ) ^ K)) ≤ 1 :=
    caich_damping_le_one hy₀ hy₀y
  have hquot :
      smoothEnergy omega y / Real.log (y : ℝ) ≤
        C * (smoothEnergy omega y / primeEnergyNormalizer y) := by
    have hinv :
        1 / Real.log (y : ℝ) ≤ C / primeEnergyNormalizer y := by
      exact (div_le_div_iff₀ hlogy hZpos).2 (by simpa using! hZupper)
    calc
      smoothEnergy omega y / Real.log (y : ℝ) =
          smoothEnergy omega y * (1 / Real.log (y : ℝ)) := by ring
      _ ≤ smoothEnergy omega y * (C / primeEnergyNormalizer y) :=
        mul_le_mul_of_nonneg_left hinv hH
      _ = C * (smoothEnergy omega y / primeEnergyNormalizer y) := by ring
  unfold caichNormalizedEnergy exactNormalizedEnergy
  calc
    (2 * Real.pi) *
          Real.exp
            (-Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
              ((ell : ℝ) ^ K)) *
          (smoothEnergy omega y / Real.log (y : ℝ)) ≤
        (2 * Real.pi) * 1 *
          (smoothEnergy omega y / Real.log (y : ℝ)) := by
      gcongr
    _ ≤ (2 * Real.pi) *
          (C * (smoothEnergy omega y / primeEnergyNormalizer y)) := by
      have htwoPi : 0 ≤ (2 * Real.pi : ℝ) :=
        mul_nonneg (by norm_num) Real.pi_pos.le
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left hquot htwoPi
    _ = (2 * Real.pi * C) *
          (smoothEnergy omega y / primeEnergyNormalizer y) := by ring

/-- At the initial cutoff the damping factor is exactly one. -/
theorem caichNormalizedEnergy_initial_eq
    (ell K y₀ : ℕ) (hy₀ : 1 < y₀) (omega : Omega) :
    caichNormalizedEnergy ell K y₀ y₀ omega =
      (2 * Real.pi) * smoothEnergy omega y₀ /
        Real.log (y₀ : ℝ) := by
  have hlog : Real.log (y₀ : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hy₀)).ne'
  unfold caichNormalizedEnergy
  rw [div_self hlog, Real.log_one, neg_zero, zero_div, Real.exp_zero]
  ring

/-- A lower Mertens-product inequality at the initial cutoff bounds the exact
martingale normalization by Caich's normalization. -/
theorem exactNormalizedEnergy_le_mul_caichNormalizedEnergy_initial
    {ell K y₀ : ℕ} (hy₀ : 1 < y₀) {c : ℝ} (hc : 0 < c)
    (hZlower : c * Real.log (y₀ : ℝ) ≤ primeEnergyNormalizer y₀)
    (omega : Omega) :
    exactNormalizedEnergy omega y₀ ≤
      (1 / (2 * Real.pi * c)) *
        caichNormalizedEnergy ell K y₀ y₀ omega := by
  have hlog : 0 < Real.log (y₀ : ℝ) :=
    Real.log_pos (by exact_mod_cast hy₀)
  have hcLog : 0 < c * Real.log (y₀ : ℝ) := mul_pos hc hlog
  have hH : 0 ≤ smoothEnergy omega y₀ := smoothEnergy_nonneg omega y₀
  unfold exactNormalizedEnergy
  calc
    smoothEnergy omega y₀ / primeEnergyNormalizer y₀ ≤
        smoothEnergy omega y₀ /
          (c * Real.log (y₀ : ℝ)) :=
      div_le_div_of_nonneg_left hH hcLog hZlower
    _ = (1 / (2 * Real.pi * c)) *
          caichNormalizedEnergy ell K y₀ y₀ omega := by
      rw [caichNormalizedEnergy_initial_eq ell K y₀ hy₀ omega]
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp

/-! ## Transfer of Harper's low fractional moment -/

/-- Harper's `2/3` moment estimate for Caich's initial energy transfers to
the exact martingale energy, with only the deterministic comparison constant
raised to the `2/3` power. -/
theorem integral_exactNormalizedEnergy_rpow_twoThird_le_of_caich
    {ell K y₀ : ℕ} (hy₀ : 1 < y₀) {c L : ℝ} (hc : 0 < c)
    (hZlower : c * Real.log (y₀ : ℝ) ≤ primeEnergyNormalizer y₀)
    (hCaichMoment :
      (∫ omega,
        caichNormalizedEnergy ell K y₀ y₀ omega ^ ((2 : ℝ) / 3) ∂μ) ≤ L) :
    (∫ omega,
      exactNormalizedEnergy omega y₀ ^ ((2 : ℝ) / 3) ∂μ) ≤
      (1 / (2 * Real.pi * c)) ^ ((2 : ℝ) / 3) * L := by
  let d : ℝ := 1 / (2 * Real.pi * c)
  have hd : 0 ≤ d := by
    unfold d
    positivity
  have hExactInt : Integrable
      (fun omega : Omega =>
        exactNormalizedEnergy omega y₀ ^ ((2 : ℝ) / 3)) μ := by
    apply integrable_rpow_of_integrable_nonneg
      (integrable_exactNormalizedEnergy y₀)
      (fun omega => exactNormalizedEnergy_nonneg omega y₀)
    · norm_num
    · norm_num
  have hCaichInt : Integrable
      (fun omega : Omega =>
        caichNormalizedEnergy ell K y₀ y₀ omega ^ ((2 : ℝ) / 3)) μ := by
    apply integrable_rpow_of_integrable_nonneg
      (integrable_caichNormalizedEnergy ell K y₀ y₀)
      (fun omega => caichNormalizedEnergy_nonneg hy₀ omega)
    · norm_num
    · norm_num
  have hpoint (omega : Omega) :
      exactNormalizedEnergy omega y₀ ^ ((2 : ℝ) / 3) ≤
        d ^ ((2 : ℝ) / 3) *
          caichNormalizedEnergy ell K y₀ y₀ omega ^ ((2 : ℝ) / 3) := by
    have hbase := exactNormalizedEnergy_le_mul_caichNormalizedEnergy_initial
      (ell := ell) (K := K) hy₀ hc hZlower omega
    change exactNormalizedEnergy omega y₀ ≤
      d * caichNormalizedEnergy ell K y₀ y₀ omega at hbase
    have hrpow :
        exactNormalizedEnergy omega y₀ ^ ((2 : ℝ) / 3) ≤
          (d * caichNormalizedEnergy ell K y₀ y₀ omega) ^
            ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (exactNormalizedEnergy_nonneg omega y₀) hbase
        (by norm_num)
    rw [Real.mul_rpow hd (caichNormalizedEnergy_nonneg hy₀ omega)] at hrpow
    exact hrpow
  calc
    (∫ omega,
        exactNormalizedEnergy omega y₀ ^ ((2 : ℝ) / 3) ∂μ) ≤
        ∫ omega,
          d ^ ((2 : ℝ) / 3) *
            caichNormalizedEnergy ell K y₀ y₀ omega ^ ((2 : ℝ) / 3) ∂μ := by
      exact integral_mono hExactInt (hCaichInt.const_mul _) hpoint
    _ = d ^ ((2 : ℝ) / 3) *
          ∫ omega,
            caichNormalizedEnergy ell K y₀ y₀ omega ^ ((2 : ℝ) / 3) ∂μ := by
      rw [integral_const_mul]
    _ ≤ d ^ ((2 : ℝ) / 3) * L :=
      mul_le_mul_of_nonneg_left hCaichMoment (Real.rpow_nonneg hd _)

/-- Version of the moment transfer already packaged in the scalar budget used
by `ExactEnergySmall`. -/
theorem integral_exactNormalizedEnergy_rpow_twoThird_le_caichBudget
    {ell K y₀ : ℕ} (hy₀ : 1 < y₀) {c C : ℝ} (hc : 0 < c)
    (hZlower : c * Real.log (y₀ : ℝ) ≤ primeEnergyNormalizer y₀)
    (hCaichMoment :
      (∫ omega,
        caichNormalizedEnergy ell K y₀ y₀ omega ^ ((2 : ℝ) / 3) ∂μ) ≤
          caichInitialEnergyMomentBudget ell K C) :
    (∫ omega,
      exactNormalizedEnergy omega y₀ ^ ((2 : ℝ) / 3) ∂μ) ≤
      caichInitialEnergyMomentBudget ell K
        ((1 / (2 * Real.pi * c)) ^ ((2 : ℝ) / 3) * C) := by
  have h := integral_exactNormalizedEnergy_rpow_twoThird_le_of_caich
    hy₀ hc hZlower hCaichMoment
  unfold caichInitialEnergyMomentBudget at h ⊢
  exact h.trans_eq (by ring)

/-- Direct scheduled-process form of the preceding transfer.  This is the
moment hypothesis consumed by
`measureReal_scheduledExactNormalizedEnergy_max_le_caich`. -/
theorem integral_scheduledExactNormalizedEnergy_rpow_twoThird_le_caichBudget
    (y : ℕ → ℕ) {ell K y₀ : ℕ} (hyInit : y 0 = y₀)
    (hy₀ : 1 < y₀) {c C : ℝ} (hc : 0 < c)
    (hZlower : c * Real.log (y₀ : ℝ) ≤ primeEnergyNormalizer y₀)
    (hCaichMoment :
      (∫ omega,
        caichNormalizedEnergy ell K y₀ y₀ omega ^ ((2 : ℝ) / 3) ∂μ) ≤
          caichInitialEnergyMomentBudget ell K C) :
    (∫ omega,
      scheduledExactNormalizedEnergy y 0 omega ^ ((2 : ℝ) / 3) ∂μ) ≤
      caichInitialEnergyMomentBudget ell K
        ((1 / (2 * Real.pi * c)) ^ ((2 : ℝ) / 3) * C) := by
  simpa only [scheduledExactNormalizedEnergy, hyInit] using!
    integral_exactNormalizedEnergy_rpow_twoThird_le_caichBudget
      hy₀ hc hZlower hCaichMoment

end Problem520
end Erdos
