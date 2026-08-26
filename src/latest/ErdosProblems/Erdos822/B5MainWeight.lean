/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.DeterminantMassControl

/-!
# Pointwise main-weight bound on B5-good cofactors

The determinant exponential is cancelled by the Mertens square.  On the
B5-good layer, each shifted-coefficient reciprocal mass is at most the
fixed cutoff C0, so the remaining slope exponential is at most exp(12 C0).
Thus only the reduced-coefficient scale X remains pair-dependent.
-/

namespace Erdos822

/-- On a B5-good layer, the logarithmic main weight is bounded by a fixed
constant times the reduced-collision scale. -/
theorem exists_logMassMainWeight_le_reducedScale_of_massGood :
    ∃ Cdet : ℝ, 0 < Cdet ∧
      ∀ A C C₀ : ℝ, ∀ N x m m' z y S : ℕ,
        0 ≤ A → 0 ≤ C → 0 ≤ C₀ →
        2 ≤ z → z ≤ y →
        m ∈ massGoodOddCofactors N z y C₀ →
        m' ∈ massGoodOddCofactors N z y C₀ →
        logMassMainWeight A C x m m' z y S ≤
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            C ^ 2 * Cdet ^ 2 * Real.exp (12 * C₀)) *
            (((max (x / m) (x / m') /
              reducedCollisionRight m m' + 1 : ℕ) : ℝ)) := by
  obtain ⟨Cdet, hCdet, hdet⟩ :=
    exists_logRatio_sq_mul_exp_divisorMass_upper
  refine ⟨Cdet, hCdet, ?_⟩
  intro A C C₀ N x m m' z y S hA hC hC₀ hz hzy hm hm'
  have hmMass := (mem_massGoodOddCofactors_iff.mp hm).2
  have hm'Mass := (mem_massGoodOddCofactors_iff.mp hm').2
  have hsum :
      shiftedTotientReciprocalMass m z y +
          shiftedTotientReciprocalMass m' z y ≤
        2 * C₀ := by linarith
  have hshiftExp :
      Real.exp
          (6 * (shiftedTotientReciprocalMass m z y +
            shiftedTotientReciprocalMass m' z y)) ≤
        Real.exp (12 * C₀) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdet' :=
    hdet (reducedTotientDet m m') z y hz hzy
  have hratio0 :
      0 ≤ (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 :=
    sq_nonneg _
  have hdetExp0 :
      0 ≤ Real.exp (2 * divisorReciprocalMass
        (reducedTotientDet m m') z y) :=
    (Real.exp_pos _).le
  have hcombined :
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          Real.exp
            (2 * divisorReciprocalMass (reducedTotientDet m m') z y +
              6 * (shiftedTotientReciprocalMass m z y +
                shiftedTotientReciprocalMass m' z y)) ≤
        Cdet ^ 2 * Real.exp (12 * C₀) := by
    rw [Real.exp_add]
    calc
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          (Real.exp
            (2 * divisorReciprocalMass (reducedTotientDet m m') z y) *
              Real.exp
                (6 * (shiftedTotientReciprocalMass m z y +
                  shiftedTotientReciprocalMass m' z y))) =
          ((Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            Real.exp
              (2 * divisorReciprocalMass (reducedTotientDet m m') z y)) *
              Real.exp
                (6 * (shiftedTotientReciprocalMass m z y +
                  shiftedTotientReciprocalMass m' z y)) := by ring
      _ ≤ Cdet ^ 2 *
          Real.exp
            (6 * (shiftedTotientReciprocalMass m z y +
              shiftedTotientReciprocalMass m' z y)) := by
        exact mul_le_mul_of_nonneg_right hdet'
          (Real.exp_pos _).le
      _ ≤ Cdet ^ 2 * Real.exp (12 * C₀) := by
        exact mul_le_mul_of_nonneg_left hshiftExp (sq_nonneg _)
  unfold logMassMainWeight
  dsimp only
  let X : ℝ :=
    (((max (x / m) (x / m') /
      reducedCollisionRight m m' + 1 : ℕ) : ℝ))
  have hX0 : 0 ≤ X := by
    dsimp [X]
    positivity
  have heta0 :
      0 ≤ 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    have : 0 ≤ (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
      positivity
    linarith
  calc
    X *
        ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          (C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            Real.exp
              (2 * divisorReciprocalMass (reducedTotientDet m m') z y +
                6 * (shiftedTotientReciprocalMass m z y +
                  shiftedTotientReciprocalMass m' z y)))) ≤
        X *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (C ^ 2 * (Cdet ^ 2 * Real.exp (12 * C₀)))) := by
      apply mul_le_mul_of_nonneg_left _ hX0
      apply mul_le_mul_of_nonneg_left _ heta0
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left hcombined (sq_nonneg C))
    _ =
        ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          C ^ 2 * Cdet ^ 2 * Real.exp (12 * C₀)) * X := by
      dsimp [X]
      ring

end Erdos822
