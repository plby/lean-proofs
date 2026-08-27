import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Squared sums under uniform control of deviations

The squared-degree calculation in the clique-count drift uses the mean
degree, even though the individual degrees are controlled around a separate
deterministic comparison value. The variance about the mean is no larger
than the squared deviation about that comparison value.
-/

open Finset
open scoped BigOperators

namespace Arxiv2411_18291

theorem finite_sum_sq_deviation_identity {I : Type*} (S : Finset I) (x : I → ℝ)
    (m : ℝ) :
    (∑ i ∈ S, (x i - m) ^ 2) =
      (∑ i ∈ S, x i ^ 2) - 2 * m * (∑ i ∈ S, x i) + S.card * m ^ 2 := by
  calc
    _ = ∑ i ∈ S, (x i ^ 2 - 2 * m * x i + m ^ 2) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]
      simp

theorem finite_sum_sq_deviation_le {I : Type*} (S : Finset I) (x : I → ℝ)
    (m δ : ℝ) (h : ∀ i ∈ S, |x i - m| ≤ δ) :
    (∑ i ∈ S, (x i - m) ^ 2) ≤ S.card * δ ^ 2 := by
  calc
    _ ≤ ∑ _i ∈ S, δ ^ 2 := sum_le_sum fun i hi =>
      sq_le_sq.mpr ((h i hi).trans (le_abs_self δ))
    _ = _ := by simp

theorem finite_sum_sq_bounds_of_deviation {I : Type*} (S : Finset I) (hS : S.Nonempty)
    (x : I → ℝ) (m δ : ℝ) (h : ∀ i ∈ S, |x i - m| ≤ δ) :
    (∑ i ∈ S, x i) ^ 2 / S.card ≤ (∑ i ∈ S, x i ^ 2) ∧
      (∑ i ∈ S, x i ^ 2) ≤ (∑ i ∈ S, x i) ^ 2 / S.card + S.card * δ ^ 2 := by
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  constructor
  · apply (div_le_iff₀ hn).mpr
    simpa [mul_comm] using sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) x
  · have hd := finite_sum_sq_deviation_le S x m δ h
    rw [finite_sum_sq_deviation_identity] at hd
    have hd' := mul_le_mul_of_nonneg_left hd hn.le
    have hmean := sq_nonneg ((∑ i ∈ S, x i) - (S.card : ℝ) * m)
    apply le_of_mul_le_mul_right _ hn
    rw [add_mul, div_mul_cancel₀ _ hn.ne']
    nlinarith

end Arxiv2411_18291
