/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.RefinedCollisionFiber
import ErdosProblems.Erdos980.External.Erdos822.SingularFactorControl

/-!
# Arithmetic-weight form of the collision-fiber bound

After extracting the Mertens square, the only non-universal terms in one
off-diagonal fiber are reciprocal prime masses of the reduced totient
determinant and of the two shifted coefficients.  This is the form summed
in the three-range argument.
-/

namespace Erdos822

/-- The finite deleted-slope loss is nonnegative. -/
theorem slopePrimeLoss_nonneg (h a b z y : ℕ) (hz : 2 ≤ z) :
    0 ≤ slopePrimeLoss h a b z y := by
  unfold slopePrimeLoss
  apply Finset.prod_nonneg
  intro p hp
  by_cases hslope : p ∣ a ∨ p ∣ b
  · simp only [if_pos hslope]
    exact inv_nonneg.mpr (sub_nonneg.mpr
      (Erdos851.pairShiftDensity_lt_one
        (Erdos851.mem_sievePrimes.mp hp).2.2 (by
          have hpData := Erdos851.mem_sievePrimes.mp hp
          exact lt_of_le_of_lt hz hpData.1)).le)
  · simp [hslope]

/-- The scale-sensitive fiber bound with all local Euler factors replaced by
their arithmetic prime-mass weights. -/
theorem exists_outerCollisionPairs_arithmetic_mass_bound :
    ∃ A : ℝ, 1 ≤ A ∧
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
          Erdos851.localEulerProduct Erdos851.oneShiftDensity z y ^ 2 *
            Real.exp
              (2 * divisorReciprocalMass (reducedTotientDet m m') z y +
                6 * (shiftedTotientReciprocalMass m z y +
                  shiftedTotientReciprocalMass m' z y))
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((outerCollisionPairs x m m').card : ℝ) ≤
          (X : ℝ) * ((1 + eta) * W) +
            ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hfiber⟩ :=
    outerCollisionPairs_slopeAware_reducedDet_bound_of_nonempty
  refine ⟨A, hA, ?_⟩
  intro x m m' z y S hm hm' hlarge hlarge' hy hy'
    hz hzy hyTwo hS hlog hne
  have hbound :=
    hfiber x m m' z y S hm hm' hlarge hlarge' hy hy'
      hz hzy hyTwo hS hlog hne
  dsimp only at hbound ⊢
  let V := Erdos851.localEulerProduct
    (Erdos851.pairShiftDensity (reducedTotientDet m m')) z y
  let L := slopePrimeLoss (reducedTotientDet m m')
    (reducedCollisionRight m m') (reducedCollisionLeft m m') z y
  let M := Erdos851.localEulerProduct Erdos851.oneShiftDensity z y ^ 2 *
    Real.exp (2 * divisorReciprocalMass (reducedTotientDet m m') z y)
  let R := Real.exp (6 * (shiftedTotientReciprocalMass m z y +
    shiftedTotientReciprocalMass m' z y))
  have hV : V ≤ M := by
    dsimp [V, M]
    exact pairShift_localEulerProduct_le_oneShift_sq_mul_exp_mass
      (reducedTotientDet m m') z y hz
  have hL : L ≤ R := by
    dsimp [L, R]
    exact slopePrimeLoss_reducedCollision_le_exp_shiftedTotientMass
      (reducedTotientDet m m') m m' z y hz
  have hL0 : 0 ≤ L := slopePrimeLoss_nonneg _ _ _ _ _ hz
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hVL : V * L ≤ M * R :=
    mul_le_mul hV hL hL0 hM0
  have hMR :
      M * R =
        Erdos851.localEulerProduct Erdos851.oneShiftDensity z y ^ 2 *
          Real.exp
            (2 * divisorReciprocalMass (reducedTotientDet m m') z y +
              6 * (shiftedTotientReciprocalMass m z y +
                shiftedTotientReciprocalMass m' z y)) := by
    dsimp [M, R]
    rw [mul_assoc, ← Real.exp_add]
  rw [hMR] at hVL
  have heta0 :
      0 ≤ (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    positivity
  have honeeta : 0 ≤
      1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    linarith
  have hmain :=
    mul_le_mul_of_nonneg_left hVL honeeta
  have hX0 : 0 ≤
      (((max (x / m) (x / m') /
        reducedCollisionRight m m' + 1 : ℕ) : ℝ)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmain hX0
  exact hbound.trans (by
    simpa [add_comm] using
      (add_le_add_right hscaled (((y ^ S : ℕ) : ℝ) ^ 2)))

end Erdos822
