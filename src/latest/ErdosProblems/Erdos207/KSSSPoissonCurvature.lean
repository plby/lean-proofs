/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSTrajectoryBounds

/-! # Second derivative and explicit curvature bounds for the Poisson correction -/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

def ksssPoissonCurvature (orders : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ d ∈ orders, a d * (d : ℝ) * (d - 1 : ℕ) * t ^ (d - 2)

theorem hasDerivAt_ksssPoissonRate
    (orders : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (ksssPoissonRate orders a) (ksssPoissonCurvature orders a t) t := by
  apply HasDerivAt.fun_sum
  intro d hd
  convert! (hasDerivAt_pow (d - 1) t).const_mul (a d * (d : ℝ)) using 1
  simp only [Nat.sub_sub, show 1 + 1 = (2 : ℕ) by rfl]
  ring

theorem ksssPoissonCurvature_nonneg
    (orders : Finset ℕ) (a : ℕ → ℝ) {t : ℝ}
    (ha : ∀ d ∈ orders, 0 ≤ a d) (ht : 0 ≤ t) :
    0 ≤ ksssPoissonCurvature orders a t := by
  exact sum_nonneg fun d hd ↦ mul_nonneg
    (mul_nonneg (mul_nonneg (ha d hd) (Nat.cast_nonneg d)) (Nat.cast_nonneg _))
      (pow_nonneg ht _)

theorem ksssPoissonCurvature_mul_clock_sq_le_sum
    (orders : Finset ℕ) (a b : ℕ → ℝ) {E₀ t : ℝ}
    (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d)
    (ht : 0 ≤ t) (htE : t ≤ E₀) :
    ksssPoissonCurvature orders a t * E₀ ^ 2 ≤
      ∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d := by
  have hE : 0 ≤ E₀ := ht.trans htE
  unfold ksssPoissonCurvature
  rw [sum_mul]
  apply sum_le_sum
  intro d hd
  by_cases hd2 : 2 ≤ d
  · have hpower : t ^ (d - 2) * E₀ ^ 2 ≤ E₀ ^ d := by
      calc
        t ^ (d - 2) * E₀ ^ 2 ≤ E₀ ^ (d - 2) * E₀ ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht htE _) (sq_nonneg E₀)
        _ = E₀ ^ d := by rw [← pow_add, Nat.sub_add_cancel hd2]
    calc
      _ = ((d : ℝ) * (d - 1 : ℕ)) * (a d * (t ^ (d - 2) * E₀ ^ 2)) := by ring
      _ ≤ ((d : ℝ) * (d - 1 : ℕ)) * (a d * E₀ ^ d) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpower (ha d hd))
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hab d hd) (by positivity)
  · have hsub : d - 1 = 0 := by omega
    simp [hsub]

end

end Erdos207
