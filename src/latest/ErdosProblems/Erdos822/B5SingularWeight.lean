/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B5MainWeight
import ErdosProblems.Erdos851.LocalEulerProducts

/-!
# A summation-facing B5 singular weight

The fully pointwise determinant estimate in B5MainWeight is useful for
exceptional pairs, but it spends the square logarithmic saving from the
two-prime sieve.  For the global average we keep the determinant singular
factor visible.  Condition B5 still makes the deleted-slope factor a fixed
constant, while the direct Mertens factor keeps its square logarithmic
ratio.
-/

namespace Erdos822

theorem singularFactor_nonneg (h z y : ℕ) :
    0 ≤ Erdos851.singularFactor h z y := by
  unfold Erdos851.singularFactor
  apply Finset.prod_nonneg
  intro p hp
  by_cases hph : p ∣ h
  · simp only [if_pos hph]
    have hpPrime := (Erdos851.mem_sievePrimes.mp hp).2.2
    exact div_nonneg (by positivity) (by
      have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
      linarith)
  · simp [hph]

/-- The main term before replacing the determinant singular factor by its
worst possible Mertens bound. -/
noncomputable def b5SingularMainWeight
    (A C C₀ : ℝ) (x m m' z y S : ℕ) : ℝ :=
  let X :=
    max (x / m) (x / m') / reducedCollisionRight m m' + 1
  let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  (X : ℝ) *
    ((1 + eta) *
      (C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        (Erdos851.singularFactor (reducedTotientDet m m') z y *
          Real.exp (12 * C₀))))

theorem b5SingularMainWeight_nonneg
    (A C C₀ : ℝ) (x m m' z y S : ℕ) (hA : 0 ≤ A) :
    0 ≤ b5SingularMainWeight A C C₀ x m m' z y S := by
  unfold b5SingularMainWeight
  dsimp only
  have heta :
      0 ≤ 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    have : 0 ≤ (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
      positivity
    linarith
  have hsing :
      0 ≤ Erdos851.singularFactor (reducedTotientDet m m') z y :=
    singularFactor_nonneg _ _ _
  positivity

/-- On the B5-good layer, a nonempty off-diagonal collision fiber is
bounded by the singular weight plus the beta-sieve remainder.  Unlike the
fully pointwise bound, this keeps the determinant singular factor and hence
the square logarithmic saving. -/
theorem exists_outerCollisionPairs_le_b5SingularWeight_of_massGood :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ C₀ : ℝ, ∀ x m m' z y S : ℕ,
        0 ≤ C₀ →
        0 < m → 0 < m' →
        (∀ p ∈ outerPrimes x m, m < p) →
        (∀ p ∈ outerPrimes x m', m' < p) →
        (∀ p ∈ outerPrimes x m, y < p) →
        (∀ p ∈ outerPrimes x m', y < p) →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        shiftedTotientReciprocalMass m z y ≤ C₀ →
        shiftedTotientReciprocalMass m' z y ≤ C₀ →
        (outerCollisionPairs x m m').Nonempty →
        ((outerCollisionPairs x m m').card : ℝ) ≤
          b5SingularMainWeight A C C₀ x m m' z y S +
            ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hpair⟩ :=
    outerCollisionPairs_slopeAware_reducedDet_bound_of_nonempty
  obtain ⟨C, hC, hMertens⟩ :=
    exists_oneShift_localEulerProduct_upper
  refine ⟨A, C, hA, hC, ?_⟩
  intro C₀ x m m' z y S hC₀ hm hm' hlarge hlarge' hy hy'
    hz hzy hyTwo hS hlog hmMass hm'Mass hne
  have hbound :=
    hpair x m m' z y S hm hm' hlarge hlarge' hy hy'
      hz hzy hyTwo hS hlog hne
  dsimp only at hbound
  have hsum :
      shiftedTotientReciprocalMass m z y +
          shiftedTotientReciprocalMass m' z y ≤
        2 * C₀ := by
    linarith
  have hL :
      slopePrimeLoss (reducedTotientDet m m')
          (reducedCollisionRight m m') (reducedCollisionLeft m m') z y ≤
        Real.exp (12 * C₀) := by
    calc
      slopePrimeLoss (reducedTotientDet m m')
          (reducedCollisionRight m m') (reducedCollisionLeft m m') z y ≤
          Real.exp
            (6 * (shiftedTotientReciprocalMass m z y +
              shiftedTotientReciprocalMass m' z y)) :=
        slopePrimeLoss_reducedCollision_le_exp_shiftedTotientMass
          (reducedTotientDet m m') m m' z y hz
      _ ≤ Real.exp (12 * C₀) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hV :
      Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (reducedTotientDet m m')) z y ≤
        (C * (Real.log (z : ℝ) / Real.log (y : ℝ))) ^ 2 *
          Erdos851.singularFactor (reducedTotientDet m m') z y := by
    calc
      Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (reducedTotientDet m m')) z y ≤
          Erdos851.localEulerProduct Erdos851.oneShiftDensity z y ^ 2 *
            Erdos851.singularFactor (reducedTotientDet m m') z y :=
        Erdos851.pairShift_localEulerProduct_le
          (reducedTotientDet m m') hz
      _ ≤ (C * (Real.log (z : ℝ) / Real.log (y : ℝ))) ^ 2 *
            Erdos851.singularFactor (reducedTotientDet m m') z y := by
        have hVone :=
          hMertens z y hz hzy
        have hlocal0 :
            0 ≤ Erdos851.localEulerProduct
              Erdos851.oneShiftDensity z y :=
          Erdos851.oneShift_localEulerProduct_pos.le
        have hlogz : 0 ≤ Real.log (z : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ z by omega))
        have hlogy : 0 < Real.log (y : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < y by omega))
        have hright0 :
            0 ≤ C * (Real.log (z : ℝ) / Real.log (y : ℝ)) :=
          mul_nonneg hC.le (div_nonneg hlogz hlogy.le)
        have hsq :
            Erdos851.localEulerProduct Erdos851.oneShiftDensity z y ^ 2 ≤
              (C * (Real.log (z : ℝ) / Real.log (y : ℝ))) ^ 2 :=
          (sq_le_sq₀ hlocal0 hright0).2 hVone
        exact mul_le_mul_of_nonneg_right hsq
          (singularFactor_nonneg _ _ _)
  have hL0 :
      0 ≤ slopePrimeLoss (reducedTotientDet m m')
        (reducedCollisionRight m m') (reducedCollisionLeft m m') z y :=
    slopePrimeLoss_nonneg _ _ _ _ _ hz
  have hVright0 :
      0 ≤ (C * (Real.log (z : ℝ) / Real.log (y : ℝ))) ^ 2 *
        Erdos851.singularFactor (reducedTotientDet m m') z y := by
    exact mul_nonneg (sq_nonneg _) (singularFactor_nonneg _ _ _)
  have hVL :=
    mul_le_mul hV hL hL0 hVright0
  have heta0 :
      0 ≤ 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    have : 0 ≤ (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
      positivity
    linarith
  have hX0 :
      0 ≤ (((max (x / m) (x / m') /
        reducedCollisionRight m m' + 1 : ℕ) : ℝ)) := by
    positivity
  have hmain :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hVL heta0) hX0
  calc
    ((outerCollisionPairs x m m').card : ℝ) ≤
        (((max (x / m) (x / m') /
            reducedCollisionRight m m' + 1 : ℕ) : ℝ)) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (Erdos851.localEulerProduct
                (Erdos851.pairShiftDensity (reducedTotientDet m m')) z y *
              slopePrimeLoss (reducedTotientDet m m')
                (reducedCollisionRight m m')
                (reducedCollisionLeft m m') z y)) +
          ((y ^ S : ℕ) : ℝ) ^ 2 := hbound
    _ ≤ b5SingularMainWeight A C C₀ x m m' z y S +
          ((y ^ S : ℕ) : ℝ) ^ 2 := by
      have hmain' :
          (((max (x / m) (x / m') /
              reducedCollisionRight m m' + 1 : ℕ) : ℝ)) *
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (Erdos851.localEulerProduct
                  (Erdos851.pairShiftDensity (reducedTotientDet m m')) z y *
                slopePrimeLoss (reducedTotientDet m m')
                  (reducedCollisionRight m m')
                  (reducedCollisionLeft m m') z y)) ≤
            b5SingularMainWeight A C C₀ x m m' z y S := by
        unfold b5SingularMainWeight
        dsimp only
        calc
          (((max (x / m) (x / m') /
              reducedCollisionRight m m' + 1 : ℕ) : ℝ)) *
              ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                (Erdos851.localEulerProduct
                    (Erdos851.pairShiftDensity (reducedTotientDet m m')) z y *
                  slopePrimeLoss (reducedTotientDet m m')
                    (reducedCollisionRight m m')
                    (reducedCollisionLeft m m') z y)) ≤
              (((max (x / m) (x / m') /
                  reducedCollisionRight m m' + 1 : ℕ) : ℝ)) *
                ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                  ((C * (Real.log (z : ℝ) / Real.log (y : ℝ))) ^ 2 *
                    Erdos851.singularFactor (reducedTotientDet m m') z y *
                      Real.exp (12 * C₀))) := hmain
          _ = (((max (x / m) (x / m') /
                  reducedCollisionRight m m' + 1 : ℕ) : ℝ)) *
                ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                  (C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
                    (Erdos851.singularFactor
                      (reducedTotientDet m m') z y *
                        Real.exp (12 * C₀)))) := by ring
      exact add_le_add hmain' (le_refl _)

end Erdos822
