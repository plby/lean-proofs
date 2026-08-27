/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FinePerturbedOuterQuadraticBarrier

/-!
# Real algebra for the fine outer corridor

These lemmas isolate the two scale-free calculations at time zero.  They are
stated over `ℝ`, so later cardinal arithmetic only has to establish a bound
on the relative eligible-pair defect and the integer rounding margin.
-/

namespace Erdos207

noncomputable section

lemma fine_upper_coefficient_margin {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 100) :
    4 ≤ (4 + 64 * epsilon) * (1 - 3 * epsilon) ^ 2 := by
  have hlinear : 0 ≤ 40 - 348 * epsilon := by nlinarith
  have hcubic : 0 ≤ epsilon * (40 - 348 * epsilon + 576 * epsilon ^ 2) := by
    positivity
  nlinarith

/-- If the exact eligible-pair count is within relative defect `3ε` of
`N²/2`, the upper coefficient `4 + 64ε` starts above degree `N`. -/
lemma fine_upper_initial_crossmul {N E epsilon : ℝ}
    (hN : 0 ≤ N) (hE : 0 ≤ E)
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 100)
    (hpair : N ^ 2 * (1 - 3 * epsilon) ≤ 2 * E) :
    N ^ 4 ≤ (4 + 64 * epsilon) * E ^ 2 := by
  have hfactor : 0 ≤ 1 - 3 * epsilon := by nlinarith
  have hbase : 0 ≤ N ^ 2 * (1 - 3 * epsilon) := mul_nonneg (sq_nonneg N) hfactor
  have hsquare : (N ^ 2 * (1 - 3 * epsilon)) ^ 2 ≤ (2 * E) ^ 2 := by
    nlinarith [sq_nonneg (2 * E - N ^ 2 * (1 - 3 * epsilon))]
  have hcoefficient := fine_upper_coefficient_margin hepsilon hsmall
  have hleft : 4 * N ^ 4 ≤
      ((4 + 64 * epsilon) * (1 - 3 * epsilon) ^ 2) * N ^ 4 := by
    exact mul_le_mul_of_nonneg_right hcoefficient (by positivity)
  have hright :
      (4 + 64 * epsilon) * (N ^ 2 * (1 - 3 * epsilon)) ^ 2 ≤
        (4 + 64 * epsilon) * (2 * E) ^ 2 := by
    apply mul_le_mul_of_nonneg_left hsquare
    nlinarith
  nlinarith [hleft, hright]

/-- The lower coefficient has an exact linear safety margin. -/
lemma fine_lower_coefficient_margin {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 16) :
    0 ≤ 4 - 64 * epsilon ∧
      4 - 64 * epsilon = 4 * (1 - 16 * epsilon) := by
  constructor
  · nlinarith
  · ring

/-- An eligible-pair count at most `N²/2` puts the lower quadratic initial
value below `(1-16ε)N` after cross multiplication. -/
lemma fine_lower_initial_crossmul {N E epsilon : ℝ}
    (hN : 0 ≤ N) (hE : 0 ≤ E)
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 16)
    (hpair : 2 * E ≤ N ^ 2) :
    (4 - 64 * epsilon) * E ^ 2 ≤
      (1 - 16 * epsilon) * N ^ 4 := by
  obtain ⟨hcoeff, hcoeffEq⟩ :=
    fine_lower_coefficient_margin hepsilon hsmall
  have hsq : (2 * E) ^ 2 ≤ (N ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (N ^ 2 - 2 * E)]
  rw [hcoeffEq]
  have hmargin : 0 ≤ 1 - 16 * epsilon := by nlinarith
  nlinarith

lemma le_mul_inv_cube_of_pow_four_le {N C E : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) (hcross : N ^ 4 ≤ C * E ^ 2) :
    N ≤ C * E ^ 2 * N⁻¹ ^ 3 := by
  have hinv : 0 ≤ N⁻¹ ^ 3 := by positivity
  calc
    N = N ^ 4 * N⁻¹ ^ 3 := by field_simp
    _ ≤ (C * E ^ 2) * N⁻¹ ^ 3 :=
      mul_le_mul_of_nonneg_right hcross hinv
    _ = C * E ^ 2 * N⁻¹ ^ 3 := by ring

lemma mul_inv_cube_le_of_crossmul {N C E margin : ℝ}
    (hN : 0 < N) (hcross : C * E ^ 2 ≤ margin * N ^ 4) :
    C * E ^ 2 * N⁻¹ ^ 3 ≤ margin * N := by
  have hinv : 0 ≤ N⁻¹ ^ 3 := by positivity
  calc
    C * E ^ 2 * N⁻¹ ^ 3 ≤
        (margin * N ^ 4) * N⁻¹ ^ 3 :=
      mul_le_mul_of_nonneg_right hcross hinv
    _ = margin * N := by field_simp

end

end Erdos207
