/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.ArithmeticFiberMajorant
import ErdosProblems.Erdos822.MertensUpper

/-!
# Logarithmic collision-fiber majorant

This is the summation-facing version of the fixed-fiber bound.  The universal
two-prime sieve factor has been replaced by its explicit squared logarithm
ratio, leaving only the arithmetic exponential weight.
-/

namespace Erdos822

/-- A collision fiber is bounded by a scale factor, the squared Mertens
ratio, and the explicit arithmetic prime-mass weight. -/
theorem exists_outerCollisionPairs_log_mass_bound :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ x m m' z y S : ℕ,
        0 < m → 0 < m' →
        (∀ p ∈ outerPrimes x m, m < p) →
        (∀ p ∈ outerPrimes x m', m' < p) →
        (∀ p ∈ outerPrimes x m, y < p) →
        (∀ p ∈ outerPrimes x m', y < p) →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        (outerCollisionPairs x m m').Nonempty →
        let B := reducedCollisionRight m m'
        let U := max (x / m) (x / m')
        let X := U / B + 1
        let W :=
          C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            Real.exp
              (2 * divisorReciprocalMass (reducedTotientDet m m') z y +
                6 * (shiftedTotientReciprocalMass m z y +
                  shiftedTotientReciprocalMass m' z y))
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((outerCollisionPairs x m m').card : ℝ) ≤
          (X : ℝ) * ((1 + eta) * W) +
            ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hfiber⟩ :=
    exists_outerCollisionPairs_arithmetic_mass_bound
  obtain ⟨C, hC, hMertens⟩ :=
    exists_oneShift_localEulerProduct_upper
  refine ⟨A, C, hA, hC, ?_⟩
  intro x m m' z y S hm hm' hlarge hlarge' hy hy'
    hz hzy hyTwo hS hlog hne
  have hbound :=
    hfiber x m m' z y S hm hm' hlarge hlarge' hy hy'
      hz hzy hyTwo hS hlog hne
  dsimp only at hbound ⊢
  let V := Erdos851.localEulerProduct Erdos851.oneShiftDensity z y
  let Q := C * (Real.log (z : ℝ) / Real.log (y : ℝ))
  let E := Real.exp
    (2 * divisorReciprocalMass (reducedTotientDet m m') z y +
      6 * (shiftedTotientReciprocalMass m z y +
        shiftedTotientReciprocalMass m' z y))
  have hV : V ≤ Q := by
    dsimp [V, Q]
    exact hMertens z y hz hzy
  have hV0 : 0 ≤ V := by
    dsimp [V]
    exact Erdos851.oneShift_localEulerProduct_pos.le
  have hlogz : 0 ≤ Real.log (z : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ z by omega))
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg hC.le (div_nonneg hlogz hlogy.le)
  have hsq : V ^ 2 ≤ Q ^ 2 :=
    (sq_le_sq₀ hV0 hQ0).2 hV
  have hE0 : 0 ≤ E := by
    dsimp [E]
    positivity
  have hWE : V ^ 2 * E ≤ Q ^ 2 * E :=
    mul_le_mul_of_nonneg_right hsq hE0
  have hQsq :
      Q ^ 2 =
        C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 := by
    dsimp [Q]
    ring
  rw [hQsq] at hWE
  have heta0 :
      0 ≤ (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    positivity
  have honeeta : 0 ≤
      1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    linarith
  have hmain := mul_le_mul_of_nonneg_left hWE honeeta
  have hX0 : 0 ≤
      (((max (x / m) (x / m') /
        reducedCollisionRight m m' + 1 : ℕ) : ℝ)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmain hX0
  exact hbound.trans (by
    simpa [E, mul_assoc, add_comm] using
      (add_le_add_right hscaled (((y ^ S : ℕ) : ℝ) ^ 2)))

end Erdos822
