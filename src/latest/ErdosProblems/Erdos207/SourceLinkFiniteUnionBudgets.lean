/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EventualSourceMomentBudgets

/-! # Exact ambient and future-index unions for the final link budget -/

namespace Erdos207

open Finset
open scoped NNReal

theorem finite_order_power_union_bound
    (orders : Finset ℕ) (t tests K : ℝ≥0) (d decay : ℕ) (error : ℕ → ℝ≥0)
    (ht : 1 ≤ t) (htests : tests ≤ K*t^d)
    (herror : ∀ j ∈ orders, error j ≤ 1/t^(d+decay+1))
    (hcoefficient : K*orders.card ≤ t) : tests*∑ j ∈ orders, error j ≤ 1/t^decay := by
  have hsum : (∑ j ∈ orders, error j) ≤ (orders.card : ℝ≥0)/t^(d+decay+1) := by
    calc
      _ ≤ ∑ _j ∈ orders, (1/t^(d+decay+1) : ℝ≥0) := sum_le_sum herror
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
  have hbound := finite_polynomial_union_power_decay t tests _ K orders.card d (d+decay+1) (decay+1)
    ht htests hsum (by omega)
  exact hbound.trans (inverse_power_absorb_coefficient t _ decay (zero_lt_one.trans_le ht) hcoefficient)

theorem source_link_finite_union_power_budgets
    (orders : Finset ℕ) (N ell h R : ℕ) (t degreeError : ℝ≥0) (linkError quasiError : ℕ → ℝ≥0)
    (ht : 1 ≤ t) (hN : (N : ℝ≥0) ≤ t^R)
    (hlink : ∀ j ∈ orders, linkError j ≤ 1/t^(2*R+3))
    (hdegree : degreeError ≤ 1/t^(R+3))
    (hquasi : ∀ j ∈ orders, quasiError j ≤ 1/t^(R*(2*h^2)+3))
    (horders : (orders.card : ℝ≥0) ≤ t) (hlevels : (ell*(ell+1) : ℕ) ≤ t)
    (hquasiCoefficient : ((ell*(ell+1) : ℕ)*(h^2+1 : ℕ)*(2 : ℝ≥0)^(2*h^2)*h^2)*orders.card ≤ t) :
    (N : ℝ≥0)^2*(∑ j ∈ orders, linkError j) ≤ 1/t^2 ∧
      (ell*(ell+1) : ℕ)*(N : ℝ≥0)*degreeError ≤ 1/t^2 ∧
      (ell*(ell+1) : ℕ)*((h^2+1 : ℕ)*(N+1 : ℝ≥0)^(2*h^2))*h^2*
        (∑ j ∈ orders, quasiError j) ≤ 1/t^2 := by
  have hN2 : (N : ℝ≥0)^2 ≤ 1*t^(2*R) := by
    simpa only [one_mul, ← pow_mul, Nat.mul_comm R 2] using pow_le_pow_left' hN 2
  have hlinkBound := finite_order_power_union_bound orders t ((N : ℝ≥0)^2) 1 (2*R) 2 linkError
    ht hN2 (by simpa only [Nat.add_assoc] using hlink) (by simpa only [one_mul] using horders)
  have hdegreeTests : (ell*(ell+1) : ℕ)*(N : ℝ≥0) ≤ (ell*(ell+1) : ℕ)*t^R :=
    mul_le_mul_of_nonneg_left hN zero_le
  have hdegreeBound := finite_polynomial_union_power_decay t ((ell*(ell+1) : ℕ)*(N : ℝ≥0))
    degreeError (ell*(ell+1) : ℕ) 1 R (R+3) 3 ht hdegreeTests hdegree le_rfl
  have hdegreeFinal : (ell*(ell+1) : ℕ)*(N : ℝ≥0)*degreeError ≤ 1/t^2 := by
    apply hdegreeBound.trans
    simpa only [mul_one] using inverse_power_absorb_coefficient t ((ell*(ell+1) : ℕ)*1) 2
      (zero_lt_one.trans_le ht) (by simpa only [mul_one] using hlevels)
  let K : ℝ≥0 := (ell*(ell+1) : ℕ)*(h^2+1 : ℕ)*2^(2*h^2)*h^2
  have hNplus : (N+1 : ℝ≥0) ≤ 2*t^R := by
    calc
      _ ≤ t^R+t^R := add_le_add hN (one_le_pow₀ ht)
      _ = _ := by ring
  have hquasiTests : (ell*(ell+1) : ℕ)*((h^2+1 : ℕ)*(N+1 : ℝ≥0)^(2*h^2))*h^2 ≤
      K*t^(R*(2*h^2)) := by
    calc
      _ ≤ (ell*(ell+1) : ℕ)*((h^2+1 : ℕ)*(2*t^R)^(2*h^2))*h^2 := by gcongr
      _ = _ := by dsimp only [K]; rw [mul_pow, pow_mul]; ring
  have hquasiBound := finite_order_power_union_bound orders t
    ((ell*(ell+1) : ℕ)*((h^2+1 : ℕ)*(N+1 : ℝ≥0)^(2*h^2))*h^2) K (R*(2*h^2)) 2 quasiError
    ht hquasiTests (by simpa only [Nat.add_assoc] using hquasi) hquasiCoefficient
  exact ⟨hlinkBound, hdegreeFinal, hquasiBound⟩

end Erdos207
