/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCrudeTailExpressions
import ErdosProblems.Erdos207.FixedMomentFailureBudget

/-! # Fixed-moment budgets with explicit polynomial losses in the prior error -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem moment_power_ratio_le (t : ℝ≥0) (J s c : ℕ)
    (ht : 1 ≤ t) (hs : J + c ≤ s) :
    t ^ J / t ^ s ≤ 1 / t ^ c := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  calc
    _ ≤ t ^ J / t ^ (J + c) :=
      div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) (pow_le_pow_right₀ ht hs)
    _ = _ := by rw [pow_add]; field_simp

theorem sourceMomentTailExpression_le_uniform
    (d s : ℕ) (t A epsilon kappa W K M Q : ℝ≥0) (D : ℕ)
    (ht : 1 ≤ t) (hK : t * kappa ≤ K) (hK1 : 1 ≤ K)
    (hM : (boundedIntersectionMomentCoefficient d s : ℝ≥0) ≤ M)
    (hW : W ≤ Q * t ^ D) :
    sourceMomentTailExpression d s A epsilon kappa W K ≤
      A * (M / t) ^ s + epsilon * (Q * t ^ D) ^ s := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hratio : (boundedIntersectionMomentCoefficient d s : ℝ≥0) * kappa / K ≤ M / t := by
    apply (div_le_div_iff₀ hK0 ht0).2
    calc
      _ = (boundedIntersectionMomentCoefficient d s : ℝ≥0) * (t * kappa) := by ring
      _ ≤ M * K := mul_le_mul hM hK zero_le zero_le
  have hWr : W / K ≤ Q * t ^ D := (div_le_self zero_le hK1).trans hW
  exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left' hratio s) zero_le)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left' hWr s) zero_le)

theorem moment_polynomial_scale_budget
    (s J c D : ℕ) (t A epsilon C M Q : ℝ≥0) (ht : 1 ≤ t) (hs : J + c ≤ s) :
    C * t ^ J * (A * (M / t) ^ s + epsilon * (Q * t ^ D) ^ s) ≤
      C * A * M ^ s / t ^ c + C * epsilon * Q ^ s * t ^ (J + D * s) := by
  calc
    _ = (C * A * M ^ s) * (t ^ J / t ^ s) + C * epsilon * Q ^ s * t ^ (J + D * s) := by
      rw [div_pow, mul_pow, ← pow_mul, pow_add]; ring
    _ ≤ (C * A * M ^ s) * (1 / t ^ c) + C * epsilon * Q ^ s * t ^ (J + D * s) :=
      add_le_add (mul_le_mul_of_nonneg_left (moment_power_ratio_le t J s c ht hs) zero_le) le_rfl
    _ = _ := by ring

theorem finiteMoment_polynomial_budget
    {I : Type*} [Fintype I] (d : I → ℕ) (kappa W K : I → ℝ≥0)
    (s J c D : ℕ) (t A epsilon C M Q : ℝ≥0)
    (ht : 1 ≤ t) (hs : J + c ≤ s) (hcard : (Fintype.card I : ℝ≥0) ≤ C * t ^ J)
    (hK : ∀ i, t * kappa i ≤ K i) (hK1 : ∀ i, 1 ≤ K i)
    (hM : ∀ i, (boundedIntersectionMomentCoefficient (d i) s : ℝ≥0) ≤ M)
    (hW : ∀ i, W i ≤ Q * t ^ D) :
    (∑ i, sourceMomentTailExpression (d i) s A epsilon (kappa i) (W i) (K i)) ≤
      C * A * M ^ s / t ^ c + C * epsilon * Q ^ s * t ^ (J + D * s) := by
  have hsum : (∑ i, sourceMomentTailExpression (d i) s A epsilon (kappa i) (W i) (K i)) ≤
      (Fintype.card I : ℝ≥0) * (A * (M / t) ^ s + epsilon * (Q * t ^ D) ^ s) := by
    simpa only [sum_const, card_univ, nsmul_eq_mul] using
      sum_le_sum (s := (univ : Finset I)) (fun i _ ↦
        sourceMomentTailExpression_le_uniform (d i) s t A epsilon (kappa i) (W i) (K i) M Q D
          ht (hK i) (hK1 i) (hM i) (hW i))
  calc
    _ ≤ C * t ^ J * (A * (M / t) ^ s + epsilon * (Q * t ^ D) ^ s) :=
      hsum.trans (mul_le_mul_of_nonneg_right hcard zero_le)
    _ ≤ _ := moment_polynomial_scale_budget s J c D t A epsilon C M Q ht hs

theorem finiteMoment_polynomial_prior_error_budget
    {I : Type*} [Fintype I] (d : I → ℕ) (kappa W K : I → ℝ≥0)
    (s J c D L : ℕ) (t A epsilon C M Q B : ℝ≥0)
    (ht : 1 ≤ t) (hs : J + c ≤ s) (hL : J + D * s + c ≤ L)
    (hcard : (Fintype.card I : ℝ≥0) ≤ C * t ^ J)
    (hK : ∀ i, t * kappa i ≤ K i) (hK1 : ∀ i, 1 ≤ K i)
    (hM : ∀ i, (boundedIntersectionMomentCoefficient (d i) s : ℝ≥0) ≤ M)
    (hW : ∀ i, W i ≤ Q * t ^ D) (hepsilon : epsilon ≤ A * B / t ^ L) :
    (∑ i, sourceMomentTailExpression (d i) s A epsilon (kappa i) (W i) (K i)) ≤
      C * A * (M ^ s + B * Q ^ s) / t ^ c := by
  have htail := finiteMoment_polynomial_budget d kappa W K s J c D t A epsilon C M Q
    ht hs hcard hK hK1 hM hW
  have herr : C * epsilon * Q ^ s * t ^ (J + D * s) ≤ C * A * B * Q ^ s / t ^ c := by
    calc
      _ ≤ C * (A * B / t ^ L) * Q ^ s * t ^ (J + D * s) := by gcongr
      _ = (C * A * B * Q ^ s) * (t ^ (J + D * s) / t ^ L) := by ring
      _ ≤ (C * A * B * Q ^ s) * (1 / t ^ c) :=
        mul_le_mul_of_nonneg_left (moment_power_ratio_le t (J + D * s) L c ht hL) zero_le
      _ = _ := by ring
  exact (htail.trans (add_le_add le_rfl herr)).trans_eq (by ring)

end

end Erdos207
