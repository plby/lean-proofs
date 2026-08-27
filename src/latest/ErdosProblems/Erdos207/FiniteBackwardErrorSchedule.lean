/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib

/-! # Finite reverse error budgets for the corrected master induction -/

namespace Erdos207

open scoped NNReal

theorem exists_finite_backward_exponents
    (ell target : ℕ) (required : Fin ell → ℕ → ℕ) :
    ∃ exponent : Fin (ell + 1) → ℕ,
      target ≤ exponent (Fin.last ell) ∧
      ∀ i : Fin ell, exponent i.succ + 1 ≤ exponent i.castSucc ∧
        required i (exponent i.succ + 1) ≤ exponent i.castSucc := by
  induction ell with
  | zero =>
      exact ⟨fun _ ↦ target, le_rfl, fun i ↦ Fin.elim0 i⟩
  | succ ell ih =>
      obtain ⟨tail, hlast, hstep⟩ := ih (fun i ↦ required i.succ)
      let head := max (tail 0 + 1) (required 0 (tail 0 + 1))
      refine ⟨Fin.cases head tail, ?_, ?_⟩
      · simpa only [show Fin.last (ell + 1) = (Fin.last ell).succ from rfl, Fin.cases_succ] using hlast
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact ⟨le_max_left _ _, le_max_right _ _⟩
        · simpa only [Fin.castSucc_succ, Fin.cases_succ] using hstep j

theorem exists_finite_backward_error_schedule
    (ell target : ℕ) (minimum : Fin ell → ℕ) (required : Fin ell → ℕ → ℕ) :
    ∃ exponent : Fin (ell + 1) → ℕ, ∃ cutoff : Fin ell → ℕ,
      target ≤ exponent (Fin.last ell) ∧
      ∀ i : Fin ell,
        minimum i ≤ cutoff i ∧ exponent i.succ + 1 ≤ cutoff i ∧
        cutoff i ≤ exponent i.castSucc ∧
        required i (cutoff i) ≤ exponent i.castSucc := by
  obtain ⟨exponent, hlast, hstep⟩ := exists_finite_backward_exponents ell target
    (fun i m ↦ max (max (minimum i) m) (required i (max (minimum i) m)))
  refine ⟨exponent, fun i ↦ max (minimum i) (exponent i.succ + 1), hlast, ?_⟩
  intro i
  exact ⟨le_max_left _ _, le_max_right _ _,
    (le_max_left _ _).trans (hstep i).2, (le_max_right _ _).trans (hstep i).2⟩

theorem polynomial_error_budget_step
    (t B error : ℝ≥0) (incoming outgoing cutoff : ℕ)
    (ht : 2 ≤ t) (hB : 1 ≤ B) (hincoming : outgoing + 1 ≤ incoming)
    (hcutoff : outgoing + 1 ≤ cutoff) (herror : error ≤ 1 / t ^ cutoff) :
    B / t ^ incoming + error ≤ B / t ^ outgoing := by
  have ht1 : 1 ≤ t := (by norm_num : (1 : ℝ≥0) ≤ 2).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hmain : B / t ^ incoming ≤ B / t ^ (outgoing + 1) :=
    div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) (pow_le_pow_right₀ ht1 hincoming)
  have herr : error ≤ 1 / t ^ (outgoing + 1) := herror.trans
    (one_div_le_one_div_of_le (pow_pos ht0 _) (pow_le_pow_right₀ ht1 hcutoff))
  have hnum : B + 1 ≤ B * t := by nlinarith only [hB, mul_le_mul_of_nonneg_left ht (show 0 ≤ B from zero_le)]
  calc
    _ ≤ B / t ^ (outgoing + 1) + 1 / t ^ (outgoing + 1) := add_le_add hmain herr
    _ = (B + 1) / t ^ (outgoing + 1) := (add_div _ _ _).symm
    _ ≤ (B * t) / t ^ (outgoing + 1) := div_le_div_of_nonneg_right hnum zero_le
    _ = _ := by rw [pow_succ]; field_simp

theorem polynomial_incoming_error_budget
    (t B : ℝ≥0) (incoming required : ℕ) (ht : 1 ≤ t) (hrequired : required ≤ incoming) :
    B / t ^ incoming ≤ B / t ^ required :=
  div_le_div_of_nonneg_left zero_le (pow_pos (zero_lt_one.trans_le ht) _)
    (pow_le_pow_right₀ ht hrequired)

end Erdos207
