import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos
namespace Problem520

/-!
# Scalar algebra for the small-prime part of the `W` estimate

This file records the real-power calculation behind the short-support
interpolation estimate.  It is deliberately independent of the arithmetic
and probabilistic definitions used elsewhere in the proof.
-/

/-- The exponent contributed by the short-support cardinality. -/
noncomputable def caichWCardExponent (r : ℕ) : ℝ :=
  1 / (2 * (r : ℝ))

/-- The remaining exponent after interpolation with the divisor energy. -/
noncomputable def caichWEnergyExponent (r : ℕ) : ℝ :=
  ((2 * r - 1 : ℕ) : ℝ) / (2 * (r : ℝ))

/-- The logarithmic exponent in the raw small-prime root budget. -/
noncomputable def caichWLogExponent (r : ℕ) : ℝ :=
  4 * (r : ℝ) - 6 + 2 / (r : ℝ)

/-- The harmless `r`-dependent power of two in the scalar estimate. -/
noncomputable def caichWScalarConstant (r : ℕ) : ℝ :=
  (2 : ℝ) ^ (caichWCardExponent r + caichWLogExponent r)

/-- The power of the logarithm used in Caich's smoothing parameter. -/
def caichWScalarSmoothingExponent (r : ℕ) : ℕ :=
  8 * r ^ 2 - 8 * r + 4

theorem caichW_card_add_energy_exponent {r : ℕ} (hr : 1 ≤ r) :
    caichWCardExponent r + caichWEnergyExponent r = 1 := by
  unfold caichWCardExponent caichWEnergyExponent
  have hrR : (r : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
  field_simp
  ring

theorem caichW_divisor_log_exponent {r : ℕ} (hr : 1 ≤ r) :
    ((4 * r - 4 : ℕ) : ℝ) * caichWEnergyExponent r =
      caichWLogExponent r := by
  unfold caichWEnergyExponent caichWLogExponent
  have hrR : (r : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub (by omega : 4 ≤ 4 * r),
    Nat.cast_sub (by omega : 1 ≤ 2 * r)]
  field_simp
  ring

/-- The smoothing exponent exceeds the raw logarithmic exponent by exactly
two after multiplication by the cardinality exponent. -/
theorem caichW_smoothing_exponent_identity {r : ℕ} (hr : 1 ≤ r) :
    (caichWScalarSmoothingExponent r : ℝ) * caichWCardExponent r =
      caichWLogExponent r + 2 := by
  have hrr : r ≤ r ^ 2 := by nlinarith
  have hsub : 8 * r ≤ 8 * r ^ 2 := Nat.mul_le_mul_left 8 hrr
  unfold caichWScalarSmoothingExponent caichWCardExponent caichWLogExponent
  have hrR : (r : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub hsub]
  field_simp
  ring

theorem caichWCardExponent_pos {r : ℕ} (hr : 1 ≤ r) :
    0 < caichWCardExponent r := by
  unfold caichWCardExponent
  positivity

theorem caichWScalarConstant_pos (r : ℕ) :
    0 < caichWScalarConstant r := by
  unfold caichWScalarConstant
  positivity

/-- Exact square-root interpolation identity used for the short-support
Bonami budget. -/
theorem caichW_sqrt_interpolation
    {r : ℕ} (hr : 1 ≤ r) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (Real.sqrt A * Real.sqrt (B ^ (2 * r - 1))) ^ (1 / (r : ℝ)) =
      A ^ caichWCardExponent r * B ^ caichWEnergyExponent r := by
  have hrR : (r : ℝ) ≠ 0 := by positivity
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.mul_rpow (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg (pow_nonneg hB.le _) _),
    ← Real.rpow_mul hA.le]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hB.le, ← Real.rpow_mul hB.le]
  congr 1
  · unfold caichWCardExponent
    field_simp
  · unfold caichWEnergyExponent
    field_simp

/-- Exact algebraic form of the raw short-support/divisor-energy root
budget.  All dependence on `u`, `X`, and the logarithmic variable `L` is
displayed explicitly. -/
theorem caichW_raw_scalar_identity
    {r : ℕ} (hr : 1 ≤ r) {u X L : ℝ}
    (hu : 0 < u) (hX : 0 < X) (hL : 0 < L) :
    (Real.sqrt (2 * u / X) *
        Real.sqrt ((u * (2 * L) ^ (4 * r - 4)) ^ (2 * r - 1))) ^
        (1 / (r : ℝ)) =
      caichWScalarConstant r * u * L ^ caichWLogExponent r /
        X ^ caichWCardExponent r := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have htwoL : 0 < (2 : ℝ) * L := mul_pos htwo hL
  have hA : 0 < (2 : ℝ) * u / X := div_pos (mul_pos htwo hu) hX
  have hB : 0 < u * ((2 : ℝ) * L) ^ (4 * r - 4) :=
    mul_pos hu (pow_pos htwoL _)
  rw [caichW_sqrt_interpolation hr hA hB]
  rw [Real.div_rpow (mul_nonneg htwo.le hu.le) hX.le,
    Real.mul_rpow htwo.le hu.le,
    Real.mul_rpow hu.le (pow_nonneg htwoL.le _)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul htwoL.le,
    caichW_divisor_log_exponent hr,
    Real.mul_rpow htwo.le hL.le]
  calc
    (2 ^ caichWCardExponent r * u ^ caichWCardExponent r /
          X ^ caichWCardExponent r) *
        (u ^ caichWEnergyExponent r *
          (2 ^ caichWLogExponent r * L ^ caichWLogExponent r)) =
        (2 ^ caichWCardExponent r * 2 ^ caichWLogExponent r) *
          (u ^ caichWCardExponent r * u ^ caichWEnergyExponent r) *
          L ^ caichWLogExponent r / X ^ caichWCardExponent r := by ring
    _ = caichWScalarConstant r * u * L ^ caichWLogExponent r /
          X ^ caichWCardExponent r := by
      rw [← Real.rpow_add htwo,
        ← Real.rpow_add hu,
        caichW_card_add_energy_exponent hr,
        Real.rpow_one]
      rfl

/-- Equivalent multiplicative form, convenient when the smoothing lower
bound is used with a negative real exponent. -/
theorem caichW_raw_scalar_identity_neg
    {r : ℕ} (hr : 1 ≤ r) {u X L : ℝ}
    (hu : 0 < u) (hX : 0 < X) (hL : 0 < L) :
    (Real.sqrt (2 * u / X) *
        Real.sqrt ((u * (2 * L) ^ (4 * r - 4)) ^ (2 * r - 1))) ^
        (1 / (r : ℝ)) =
      caichWScalarConstant r * u *
        X ^ (-caichWCardExponent r) * L ^ caichWLogExponent r := by
  rw [caichW_raw_scalar_identity hr hu hX hL,
    Real.rpow_neg hX.le]
  ring

/-- Raising half of the smoothing power to the negative cardinality
exponent produces exactly the inverse-square logarithmic factor, up to one
fixed power of two. -/
theorem caichW_half_smoothing_rpow_neg
    {r : ℕ} (hr : 1 ≤ r) {L : ℝ} (hL : 0 < L) :
    (L ^ caichWScalarSmoothingExponent r / 2) ^
        (-caichWCardExponent r) =
      2 ^ caichWCardExponent r *
        L ^ (-(caichWLogExponent r + 2)) := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  rw [Real.div_rpow (pow_nonneg hL.le _) htwo.le]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hL.le]
  rw [show (caichWScalarSmoothingExponent r : ℝ) *
      (-caichWCardExponent r) = -(caichWLogExponent r + 2) by
        rw [mul_neg, caichW_smoothing_exponent_identity hr]]
  rw [Real.rpow_neg htwo.le]
  simp only [div_eq_mul_inv, inv_inv]
  ring

/-- The complete scalar saving in the small-prime range.  A lower bound by
half of the nominal smoothing parameter is enough to leave `L⁻²`. -/
theorem caichW_raw_scalar_le_rpow_neg_two
    {r : ℕ} (hr : 1 ≤ r) {u X L : ℝ}
    (hu : 0 < u) (hX : 0 < X) (hL : 0 < L)
    (hXL : L ^ caichWScalarSmoothingExponent r / 2 ≤ X) :
    (Real.sqrt (2 * u / X) *
        Real.sqrt ((u * (2 * L) ^ (4 * r - 4)) ^ (2 * r - 1))) ^
        (1 / (r : ℝ)) ≤
      (caichWScalarConstant r * 2 ^ caichWCardExponent r) * u *
        L ^ (-2 : ℝ) := by
  have hhalf : 0 < L ^ caichWScalarSmoothingExponent r / 2 := by
    positivity
  have hneg : -caichWCardExponent r ≤ 0 :=
    neg_nonpos.mpr (caichWCardExponent_pos hr).le
  have hsmooth :
      X ^ (-caichWCardExponent r) ≤
        (L ^ caichWScalarSmoothingExponent r / 2) ^
          (-caichWCardExponent r) :=
    Real.rpow_le_rpow_of_nonpos hhalf hXL hneg
  rw [caichW_raw_scalar_identity_neg hr hu hX hL]
  calc
    caichWScalarConstant r * u * X ^ (-caichWCardExponent r) *
          L ^ caichWLogExponent r ≤
        caichWScalarConstant r * u *
            (L ^ caichWScalarSmoothingExponent r / 2) ^
              (-caichWCardExponent r) *
          L ^ caichWLogExponent r := by
      apply mul_le_mul_of_nonneg_right _
        (Real.rpow_nonneg hL.le _)
      exact mul_le_mul_of_nonneg_left hsmooth
        (mul_nonneg (caichWScalarConstant_pos r).le hu.le)
    _ = (caichWScalarConstant r * 2 ^ caichWCardExponent r) * u *
          L ^ (-2 : ℝ) := by
      rw [caichW_half_smoothing_rpow_neg hr hL]
      calc
        caichWScalarConstant r * u *
              (2 ^ caichWCardExponent r *
                L ^ (-(caichWLogExponent r + 2))) *
              L ^ caichWLogExponent r =
            (caichWScalarConstant r * 2 ^ caichWCardExponent r) * u *
              (L ^ (-(caichWLogExponent r + 2)) *
                L ^ caichWLogExponent r) := by ring
        _ = (caichWScalarConstant r * 2 ^ caichWCardExponent r) * u *
              L ^ (-2 : ℝ) := by
          rw [← Real.rpow_add hL]
          have hexp : -(caichWLogExponent r + 2) +
              caichWLogExponent r = (-2 : ℝ) := by ring
          rw [hexp]

/-- Division-form version of `caichW_raw_scalar_le_rpow_neg_two`. -/
theorem caichW_raw_scalar_le_div_sq
    {r : ℕ} (hr : 1 ≤ r) {u X L : ℝ}
    (hu : 0 < u) (hX : 0 < X) (hL : 0 < L)
    (hXL : L ^ caichWScalarSmoothingExponent r / 2 ≤ X) :
    (Real.sqrt (2 * u / X) *
        Real.sqrt ((u * (2 * L) ^ (4 * r - 4)) ^ (2 * r - 1))) ^
        (1 / (r : ℝ)) ≤
      (caichWScalarConstant r * 2 ^ caichWCardExponent r) * u /
        L ^ (2 : ℕ) := by
  calc
    (Real.sqrt (2 * u / X) *
        Real.sqrt ((u * (2 * L) ^ (4 * r - 4)) ^ (2 * r - 1))) ^
        (1 / (r : ℝ)) ≤
      (caichWScalarConstant r * 2 ^ caichWCardExponent r) * u *
        L ^ (-2 : ℝ) :=
      caichW_raw_scalar_le_rpow_neg_two hr hu hX hL hXL
    _ = (caichWScalarConstant r * 2 ^ caichWCardExponent r) * u /
        L ^ (2 : ℕ) := by
      rw [Real.rpow_neg hL.le]
      simp only [div_eq_mul_inv]
      have hpow : L ^ (2 : ℝ) = L ^ (2 : ℕ) :=
        Real.rpow_natCast L 2
      rw [hpow]

end Problem520
end Erdos
