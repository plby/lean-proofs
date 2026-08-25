import ErdosProblems.Erdos237.DyadicBox

/-! Explicit margin for the dyadic S1 and S2 lower constants at radius exponent `1/8`. -/

namespace Erdos237

open Finset
open scoped BigOperators

noncomputable def dyadicS1Constant (L k : ℕ) : ℝ :=
  boxDenominator (dyadicSquareMass L k) (dyadicUpper L k) k * (1 / 2 : ℝ) ^ k

noncomputable def dyadicS2FiberConstant (L k : ℕ) : ℝ :=
  (∑ a, dyadicLinearMass L k a) ^ 2 *
    (∑ a, dyadicSquareMass L k a) ^ (k - 1) / 2 * (1 / 2 : ℝ) ^ (k + 1)

theorem dyadicS1Constant_pos {L k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    0 < dyadicS1Constant L k :=
  mul_pos (dyadic_boxDenominator_pos hL hk) (by positivity)

theorem dyadicS2FiberConstant_pos {L k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    0 < dyadicS2FiberConstant L k := by
  have hγ := sum_dyadicSquareMass_pos hL hk
  have hσ : 0 < ∑ a, dyadicLinearMass L k a := by
    unfold dyadicLinearMass
    rw [sum_dyadicHeight_mul_length hL hk]
    positivity
  unfold dyadicS2FiberConstant
  positivity

theorem dyadic_sieve_margin {L k m : ℕ} (hL : 0 < L) (hk : 0 < k)
    (hlarge : 512 * (m : ℝ) < L) :
    0 < (1 / 8 : ℝ) * k * dyadicS2FiberConstant L k - m * dyadicS1Constant L k := by
  let γ := ∑ a, dyadicSquareMass L k a
  let σ := ∑ a, dyadicLinearMass L k a
  let T := γ ^ (k - 1) * (1 / 2 : ℝ) ^ k
  have hγ : 0 < γ := sum_dyadicSquareMass_pos hL hk
  have hT : 0 < T := mul_pos (pow_pos hγ _) (by positivity)
  have hscalar : (L : ℝ) / 32 < (k : ℝ) / 2 * σ ^ 2 / γ :=
    dyadic_scalar_ratio_lower_bound hL hk
  have hs := (lt_div_iff₀ hγ).mp hscalar
  have hl := mul_lt_mul_of_pos_right hlarge hγ
  have hmargin : 0 < (k : ℝ) * σ ^ 2 / 32 - m * γ := by nlinarith
  have hI : dyadicS1Constant L k ≤ γ * T := by
    have hden := boxDenominator_le (dyadicSquareMass L k) (dyadicUpper L k)
      (dyadicSquareMass_nonneg L k) k
    calc
      _ ≤ γ ^ k * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_right hden (by positivity)
      _ = _ := by
        dsimp [T]
        rw [← mul_assoc, ← pow_succ' γ (k - 1), Nat.sub_add_cancel hk]
  have hJ : dyadicS2FiberConstant L k = σ ^ 2 / 4 * T := by
    unfold dyadicS2FiberConstant
    rw [pow_succ]
    dsimp [T, σ, γ]
    ring
  rw [hJ]
  have hprod := mul_pos hmargin hT
  have hbound := mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
  nlinarith

end Erdos237
