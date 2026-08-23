/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Algebraic-integer Liouville bounds for Erdős Problem 240

This file isolates the elementary norm argument: the product of the complex
conjugates of a nonzero algebraic integer has absolute value at least one.
-/

open scoped NumberField

noncomputable section

namespace Erdos240.AlgebraicLiouville

open Finset NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The product of the absolute values of all complex embeddings is the
absolute value of the field norm. -/
theorem prod_norm_embeddings_eq_abs_norm (x : K) :
    (∏ σ : K →ₐ[ℚ] ℂ, ‖σ x‖) = |Algebra.norm ℚ x| := by
  have h := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  rw [norm_prod] at h
  rw [← h]
  rw [eq_ratCast, Rat.cast_abs, ← Real.norm_eq_abs, ← Complex.norm_real,
    Complex.ofReal_ratCast]

/-- The product of the absolute values of the conjugates of a nonzero
algebraic integer is at least one. -/
theorem one_le_prod_norm_embeddings {a : NumberField.RingOfIntegers K} (ha : a ≠ 0) :
    1 ≤ ∏ σ : K →ₐ[ℚ] ℂ, ‖σ (a : K)‖ := by
  rw [prod_norm_embeddings_eq_abs_norm, ← Algebra.coe_norm_int]
  exact_mod_cast Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

/-- Product of all conjugate absolute values except for the distinguished
embedding `σ`. -/
def otherConjugateProduct (a : K) (σ : K →ₐ[ℚ] ℂ) : ℝ := by
  classical
  exact ∏ τ ∈ Finset.univ.erase σ, ‖τ a‖

theorem otherConjugateProduct_pos {a : NumberField.RingOfIntegers K} (ha : a ≠ 0)
    (σ : K →ₐ[ℚ] ℂ) :
    0 < otherConjugateProduct (a : K) σ := by
  classical
  apply Finset.prod_pos
  intro τ hτ
  rw [norm_pos_iff]
  exact (map_ne_zero τ).mpr ((Subalgebra.coe_eq_zero _).not.mpr ha)

theorem otherConjugateProduct_pos_of_ne_zero {x : K} (hx : x ≠ 0)
    (σ : K →ₐ[ℚ] ℂ) :
    0 < otherConjugateProduct x σ := by
  classical
  apply Finset.prod_pos
  intro τ hτ
  rw [norm_pos_iff]
  exact (map_ne_zero τ).mpr hx

/-- The inverse-product bound only needs a lower bound of one for the
absolute field norm; integrality is one way to obtain that hypothesis. -/
theorem inv_otherConjugateProduct_le_norm_of_one_le_abs_norm
    {x : K} (hx : x ≠ 0) (hnorm : 1 ≤ |Algebra.norm ℚ x|)
    (σ : K →ₐ[ℚ] ℂ) :
    (otherConjugateProduct x σ)⁻¹ ≤ ‖σ x‖ := by
  classical
  have hprod : 1 ≤ ∏ τ : K →ₐ[ℚ] ℂ, ‖τ x‖ := by
    rw [prod_norm_embeddings_eq_abs_norm]
    exact_mod_cast hnorm
  rw [← Finset.mul_prod_erase Finset.univ (fun τ : K →ₐ[ℚ] ℂ ↦ ‖τ x‖)
    (Finset.mem_univ σ)] at hprod
  rw [inv_eq_one_div, div_le_iff₀ (otherConjugateProduct_pos_of_ne_zero hx σ)]
  simpa [otherConjugateProduct] using hprod

/-- **Inverse-product Liouville bound.**  A selected conjugate of a nonzero
algebraic integer is bounded below by the inverse product of all its other
conjugates. -/
theorem inv_otherConjugateProduct_le_norm {a : NumberField.RingOfIntegers K} (ha : a ≠ 0)
    (σ : K →ₐ[ℚ] ℂ) :
    (otherConjugateProduct (a : K) σ)⁻¹ ≤ ‖σ (a : K)‖ := by
  classical
  have hprod := one_le_prod_norm_embeddings (K := K) ha
  rw [← Finset.mul_prod_erase Finset.univ (fun τ : K →ₐ[ℚ] ℂ ↦ ‖τ (a : K)‖)
    (Finset.mem_univ σ)] at hprod
  rw [inv_eq_one_div, div_le_iff₀ (otherConjugateProduct_pos (K := K) ha σ)]
  simpa [otherConjugateProduct] using hprod

/-- **Uniform conjugate bound.**  If every conjugate other than `σ` has
absolute value at most `B`, then `‖σ a‖ ≥ B⁻⁽ⁿ⁻¹⁾`. -/
theorem inv_pow_finrank_sub_one_le_norm {a : NumberField.RingOfIntegers K} (ha : a ≠ 0)
    (σ : K →ₐ[ℚ] ℂ) {B : ℝ} (hB : 0 < B)
    (hother : ∀ τ : K →ₐ[ℚ] ℂ, τ ≠ σ → ‖τ (a : K)‖ ≤ B) :
    (B ^ (Module.finrank ℚ K - 1))⁻¹ ≤ ‖σ (a : K)‖ := by
  classical
  have hcard : (Finset.univ.erase σ).card = Module.finrank ℚ K - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ σ), Finset.card_univ, AlgHom.card]
  have hothers_le : otherConjugateProduct (a : K) σ ≤
      B ^ (Module.finrank ℚ K - 1) := by
    calc
      otherConjugateProduct (a : K) σ ≤
          ∏ _τ ∈ Finset.univ.erase σ, B := by
        apply Finset.prod_le_prod
        · intro τ hτ
          positivity
        · intro τ hτ
          exact hother τ (Finset.ne_of_mem_erase hτ)
      _ = B ^ (Module.finrank ℚ K - 1) := by simp [hcard]
  rw [inv_eq_one_div, div_le_iff₀ (pow_pos hB _)]
  have hprod := one_le_prod_norm_embeddings (K := K) ha
  rw [← Finset.mul_prod_erase Finset.univ (fun τ : K →ₐ[ℚ] ℂ ↦ ‖τ (a : K)‖)
    (Finset.mem_univ σ)] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_left hothers_le (norm_nonneg _))

/-- The same bound with the house of the algebraic integer as the uniform
upper bound for all other conjugates. -/
theorem inv_house_pow_le_norm {a : NumberField.RingOfIntegers K} (ha : a ≠ 0)
    (σ : K →ₐ[ℚ] ℂ) :
    (NumberField.house (a : K) ^ (Module.finrank ℚ K - 1))⁻¹ ≤
      ‖σ (a : K)‖ := by
  classical
  have haK : (a : K) ≠ 0 := (Subalgebra.coe_eq_zero _).not.mpr ha
  apply inv_pow_finrank_sub_one_le_norm (K := K) ha σ
  · exact lt_of_lt_of_le zero_lt_one
      (NumberField.one_le_house_of_isIntegral a.property haK)
  · intro τ _
    simpa using NumberField.norm_embedding_le_house (a : K) τ.toRingHom

end Erdos240.AlgebraicLiouville
