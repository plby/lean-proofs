/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SymmetricScale

/-!
# Symmetric B5 singular majorant

The collision fiber is unchanged when the two cofactors are swapped.  This
file applies the sharper B5 bound in whichever orientation puts the larger
cofactor in the right-hand primitive coefficient.
-/

namespace Erdos822

/-- The B5 singular weight with the cofactor pair sorted by size. -/
noncomputable def symmetricB5SingularMainWeight
    (A C C₀ : ℝ) (x m m' z y S : ℕ) : ℝ :=
  if m ≤ m' then
    b5SingularMainWeight A C C₀ x m m' z y S
  else
    b5SingularMainWeight A C C₀ x m' m z y S

theorem symmetricB5SingularMainWeight_nonneg
    (A C C₀ : ℝ) (x m m' z y S : ℕ) (hA : 0 ≤ A) :
    0 ≤ symmetricB5SingularMainWeight A C C₀ x m m' z y S := by
  unfold symmetricB5SingularMainWeight
  split_ifs
  · exact b5SingularMainWeight_nonneg A C C₀ x m m' z y S hA
  · exact b5SingularMainWeight_nonneg A C C₀ x m' m z y S hA

/-- After sorting, the only pair-dependent factors are the symmetric scale
and the determinant singular factor. -/
theorem symmetricB5SingularMainWeight_eq
    (A C C₀ : ℝ) (x m m' z y S : ℕ) :
    symmetricB5SingularMainWeight A C C₀ x m m' z y S =
      (symmetricReducedScale x m m' : ℝ) *
        ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          (C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (Erdos851.singularFactor (reducedTotientDet m m') z y *
              Real.exp (12 * C₀)))) := by
  by_cases hle : m ≤ m'
  · simp [symmetricB5SingularMainWeight, symmetricReducedScale, hle,
      b5SingularMainWeight, reducedScale]
  · simp [symmetricB5SingularMainWeight, symmetricReducedScale, hle,
      b5SingularMainWeight, reducedScale, reducedTotientDet_comm]

/-- The sorted B5 singular weight is bounded by the symmetric
gcd-over-product kernel.  This is the exact algebraic reduction used before
the three-range average. -/
theorem symmetricB5SingularMainWeight_le_gcdKernel
    {A C C₀ : ℝ} {x m m' z y S : ℕ}
    (hA : 0 ≤ A) (hm : 0 < m) (hm' : 0 < m') :
    symmetricB5SingularMainWeight A C C₀ x m m' z y S ≤
      (1 + ((x * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
          ((m * m' : ℕ) : ℝ)) *
        ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          (C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (Erdos851.singularFactor (reducedTotientDet m m') z y *
              Real.exp (12 * C₀)))) := by
  rw [symmetricB5SingularMainWeight_eq]
  have hscale :=
    symmetricReducedScale_cast_le_one_add_gcdWeight
      (x := x) hm hm'
  have heta :
      0 ≤ 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    have : 0 ≤ (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
      positivity
    linarith
  have hfactor :
      0 ≤ (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
        (C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          (Erdos851.singularFactor (reducedTotientDet m m') z y *
            Real.exp (12 * C₀))) := by
    exact mul_nonneg heta (mul_nonneg (mul_nonneg (sq_nonneg C)
      (sq_nonneg _)) (mul_nonneg (singularFactor_nonneg _ _ _)
        (Real.exp_pos _).le))
  exact mul_le_mul_of_nonneg_right hscale hfactor

/-- A nonempty fiber is bounded by the B5 singular weight in its sorted
orientation. -/
theorem exists_outerCollisionPairs_le_symmetricB5SingularWeight_of_massGood :
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
          symmetricB5SingularMainWeight A C C₀ x m m' z y S +
            ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, C, hA, hC, hpoint⟩ :=
    exists_outerCollisionPairs_le_b5SingularWeight_of_massGood
  refine ⟨A, C, hA, hC, ?_⟩
  intro C₀ x m m' z y S hC₀ hm hm' hlarge hlarge' hy hy'
    hz hzy hyTwo hS hlog hmass hmass' hne
  by_cases hle : m ≤ m'
  · simpa [symmetricB5SingularMainWeight, hle] using
      (hpoint C₀ x m m' z y S hC₀ hm hm' hlarge hlarge'
        hy hy' hz hzy hyTwo hS hlog hmass hmass' hne)
  · have hswapNonempty : (outerCollisionPairs x m' m).Nonempty := by
      rw [← Finset.card_pos]
      rw [← outerCollisionPairs_card_comm x m m']
      exact Finset.card_pos.mpr hne
    have hswap :=
      hpoint C₀ x m' m z y S hC₀ hm' hm hlarge' hlarge
        hy' hy hz hzy hyTwo hS hlog hmass' hmass hswapNonempty
    rw [← outerCollisionPairs_card_comm x m m'] at hswap
    simpa [symmetricB5SingularMainWeight, hle] using hswap

end Erdos822
