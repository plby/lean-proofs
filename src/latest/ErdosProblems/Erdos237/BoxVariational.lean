import ErdosProblems.Erdos237.ProductWeights
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite box model for the large-dimension variational argument

`w` is the squared mass of each one-dimensional interval, `v` its linear
mass, and `c` its upper endpoint. The expressions below are the denominator
and one face numerator for a step function supported on boxes whose upper
endpoints sum to at most one. This file proves the finite-sum estimates;
the measure-theoretic identification is not assumed or asserted here.
-/

namespace Erdos237

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def boxDenominator (w c : α → ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n → α, if (∑ i, c (x i)) ≤ 1 then ∏ i, w (x i) else 0

noncomputable def boxFaceNumerator (w v c : α → ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n → α, (∏ i, w (x i)) *
    (∑ a : α, if (∑ i, c (x i)) + c a ≤ 1 then v a else 0) ^ 2

theorem boxDenominator_le (w c : α → ℝ) (hw : ∀ a, 0 ≤ w a) (n : ℕ) :
    boxDenominator w c n ≤ (∑ a, w a) ^ n := by
  classical
  rw [Fintype.sum_pow]
  apply sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact prod_nonneg fun i _ => hw (x i)

theorem boxDenominator_pos (w c : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (n : ℕ) (a : α) (hwa : 0 < w a) (hca : (n : ℝ) * c a ≤ 1) :
    0 < boxDenominator w c n := by
  classical
  apply sum_pos'
  · intro x _
    split_ifs
    · exact prod_nonneg fun i _ => hw (x i)
    · exact le_rfl
  · refine ⟨fun _ => a, mem_univ _, ?_⟩
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hca, if_true,
      prod_const]
    exact pow_pos hwa n

omit [Fintype α] in
theorem product_weights_eq_normalized (w : α → ℝ)
    {γ : ℝ} (hγ : γ ≠ 0) (n : ℕ) (x : Fin n → α) :
    (∏ i, w (x i)) = γ ^ n * ∏ i, (w (x i) / γ) := by
  rw [prod_div_distrib]
  simp only [prod_const, card_univ, Fintype.card_fin]
  field_simp

/-- A first-moment estimate gives a lower bound for a full face integral
in the finite box model. -/
theorem boxFaceNumerator_lower_bound (w v c : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hc : ∀ a, 0 ≤ c a) (hcHalf : ∀ a, c a ≤ 1 / 2)
    (n : ℕ) (hγ : 0 < ∑ a, w a)
    (hmean : (n : ℝ) * (∑ a, c a * (w a / ∑ b, w b)) ≤ 1 / 4) :
    (∑ a, w a) ^ n / 2 * (∑ a, v a) ^ 2 ≤ boxFaceNumerator w v c n := by
  classical
  let γ := ∑ a, w a
  let prob := fun a => w a / γ
  have hprob : ∑ a, prob a = 1 := by
    dsimp [prob]
    rw [← sum_div]
    exact div_self hγ.ne'
  have hprob0 (a : α) : 0 ≤ prob a := div_nonneg (hw a) hγ.le
  have hgood := half_le_product_mass_below_cutoff (ι := Fin n)
    prob c hprob hprob0 hc (1 / 2) (by norm_num) (by
      simpa only [Fintype.card_fin, show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num]
        using hmean)
  let goodMass := ∑ x : Fin n → α,
    if (∑ i, c (x i)) ≤ 1 / 2 then ∏ i, prob (x i) else 0
  have hpoint (x : Fin n → α) :
      γ ^ n * (∑ a, v a) ^ 2 *
          (if (∑ i, c (x i)) ≤ 1 / 2 then ∏ i, prob (x i) else 0) ≤
        (∏ i, w (x i)) *
          (∑ a, if (∑ i, c (x i)) + c a ≤ 1 then v a else 0) ^ 2 := by
    split_ifs with hx
    · have hinner : (∑ a, if (∑ i, c (x i)) + c a ≤ 1 then v a else 0) =
          ∑ a, v a := by
        apply sum_congr rfl
        intro a _
        rw [if_pos (by linarith [hcHalf a])]
      rw [hinner, product_weights_eq_normalized w hγ.ne' n x]
      dsimp [prob, γ]
      exact le_of_eq (by ring)
    · simp only [mul_zero]
      exact mul_nonneg (prod_nonneg fun i _ => hw (x i)) (sq_nonneg _)
  have hbound : γ ^ n * (∑ a, v a) ^ 2 * goodMass ≤ boxFaceNumerator w v c n := by
    dsimp [goodMass, boxFaceNumerator]
    rw [mul_sum]
    exact sum_le_sum fun x _ => hpoint x
  have hnonneg : 0 ≤ γ ^ n * (∑ a, v a) ^ 2 := mul_nonneg (pow_nonneg hγ.le n) (sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hgood hnonneg
  dsimp [goodMass] at hbound
  dsimp [γ] at hscaled hbound
  nlinarith

/-- Lower bound for the ratio of the finite box numerator to denominator. -/
theorem box_ratio_lower_bound (w v c : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hc : ∀ a, 0 ≤ c a) (hcHalf : ∀ a, c a ≤ 1 / 2)
    (n : ℕ) (hγ : 0 < ∑ a, w a)
    (hmean : (n : ℝ) * (∑ a, c a * (w a / ∑ b, w b)) ≤ 1 / 4)
    (hD : 0 < boxDenominator w c (n + 1)) :
    ((n + 1 : ℕ) : ℝ) / 2 * (∑ a, v a) ^ 2 / (∑ a, w a) ≤
      ((n + 1 : ℕ) : ℝ) * boxFaceNumerator w v c n / boxDenominator w c (n + 1) := by
  have hface := boxFaceNumerator_lower_bound w v c hw hc hcHalf n hγ hmean
  have hdenom := boxDenominator_le w c hw (n + 1)
  apply (le_div_iff₀ hD).2
  calc
    _ ≤ (((n + 1 : ℕ) : ℝ) / 2 * (∑ a, v a) ^ 2 / (∑ a, w a)) *
        (∑ a, w a) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hdenom (by positivity)
    _ = ((n + 1 : ℕ) : ℝ) * ((∑ a, w a) ^ n / 2 * (∑ a, v a) ^ 2) := by
      rw [pow_succ]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hface (by positivity)

end Erdos237
