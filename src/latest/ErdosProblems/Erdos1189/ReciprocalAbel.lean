/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite summation by parts for reciprocal weights.
Informal argument: Abel summation, used for the reciprocal-sum construction.
Formal author: OpenAI Codex.
-/

import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace Erdos1189

open Finset

noncomputable def initialSum (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ range N, f (i + 1)

lemma initialSum_succ (f : ℕ → ℝ) (N : ℕ) :
    initialSum f (N + 1) = initialSum f N + f (N + 1) := by
  exact sum_range_succ _ _

lemma initialSum_eq_sum_Ioc (f : ℕ → ℝ) (N : ℕ) :
    initialSum f N = ∑ i ∈ Ioc 0 N, f i := by
  unfold initialSum
  rw [range_eq_Ico, sum_Ico_add' f 0 N (c := 1)]
  apply sum_congr
  · ext i
    simp only [mem_Ico, mem_Ioc]
    omega
  · intro i _
    rfl

lemma reciprocal_sum_eq_sum_Ioc (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range N, f (i + 1) / (i + 1 : ℝ)) =
      ∑ i ∈ Ioc 0 N, f i / i := by
  simpa only [initialSum, Nat.cast_add, Nat.cast_one] using
    initialSum_eq_sum_Ioc (fun n => f n / n) N

lemma reciprocal_abel (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range N, f (i + 1) / (i + 1 : ℝ)) =
      initialSum f N / (N + 1 : ℝ) +
        ∑ i ∈ range N, initialSum f (i + 1) *
          ((i + 1 : ℝ)⁻¹ - (i + 2 : ℝ)⁻¹) := by
  induction N with
  | zero => simp [initialSum]
  | succ N ih =>
      rw [sum_range_succ, sum_range_succ, ih, initialSum_succ]
      push_cast
      have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have hN2 : (N : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring

lemma reciprocal_prefix_mono {f g : ℕ → ℝ} {N : ℕ}
    (h : ∀ n ≤ N, initialSum f n ≤ initialSum g n) :
    (∑ i ∈ range N, f (i + 1) / (i + 1 : ℝ)) ≤
      ∑ i ∈ range N, g (i + 1) / (i + 1 : ℝ) := by
  rw [reciprocal_abel, reciprocal_abel]
  apply add_le_add
  · exact div_le_div_of_nonneg_right (h N le_rfl) (by positivity)
  · apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right (h (i + 1) (by simpa using mem_range.mp hi))
    apply sub_nonneg.mpr
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    linarith

lemma constant_reciprocal_sum (c : ℝ) (N : ℕ) :
    (∑ i ∈ range N, c / (i + 1 : ℝ)) = c * (harmonic N : ℝ) := by
  simp [harmonic, div_eq_mul_inv, mul_sum]

lemma reciprocal_lower_of_prefix {f : ℕ → ℝ} {c : ℝ} {N : ℕ}
    (h : ∀ n ≤ N, c * n ≤ initialSum f n) :
    c * (harmonic N : ℝ) ≤ ∑ i ∈ range N, f (i + 1) / (i + 1 : ℝ) := by
  rw [← constant_reciprocal_sum]
  apply reciprocal_prefix_mono (f := fun _ => c)
  intro n hn
  simpa [initialSum, mul_comm] using h n hn

lemma reciprocal_difference_sum (N : ℕ) :
    (∑ i ∈ range N, ((i + 1 : ℝ)⁻¹ - (i + 2 : ℝ)⁻¹)) +
      (N + 1 : ℝ)⁻¹ = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ]
      norm_num only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
      linarith

lemma reciprocal_lower_of_prefix_deficit {f : ℕ → ℝ} {c C : ℝ} {N : ℕ}
    (h : ∀ n ≤ N, c * n - C ≤ initialSum f n) :
    c * (harmonic N : ℝ) - C ≤
      ∑ i ∈ range N, f (i + 1) / (i + 1 : ℝ) := by
  let δ := fun i : ℕ => (i + 1 : ℝ)⁻¹ - (i + 2 : ℝ)⁻¹
  have hc : c * (harmonic N : ℝ) = c * N / (N + 1 : ℝ) +
      ∑ i ∈ range N, c * (i + 1) * δ i := by
    simpa only [constant_reciprocal_sum, initialSum, sum_const, card_range,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm] using
      reciprocal_abel (fun _ => c) N
  have hdelta : (∑ i ∈ range N, δ i) + (N + 1 : ℝ)⁻¹ = 1 :=
    reciprocal_difference_sum N
  rw [reciprocal_abel]
  calc
    c * (harmonic N : ℝ) - C =
        (c * N - C) / (N + 1 : ℝ) +
          ∑ i ∈ range N, (c * (i + 1) - C) *
            ((i + 1 : ℝ)⁻¹ - (i + 2 : ℝ)⁻¹) := by
      rw [hc]
      change _ = (c * N - C) / (N + 1 : ℝ) +
        ∑ i ∈ range N, (c * (i + 1) - C) * δ i
      simp only [sub_mul, sum_sub_distrib, ← mul_sum, sub_div]
      rw [div_eq_mul_inv C]
      linear_combination C * hdelta
    _ ≤ _ := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (h N le_rfl) (by positivity)
      · apply sum_le_sum
        intro i hi
        have hiN : i + 1 ≤ N := by simpa using mem_range.mp hi
        apply mul_le_mul_of_nonneg_right (by simpa using h (i + 1) hiN)
        apply sub_nonneg.mpr
        apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
        linarith

end Erdos1189
