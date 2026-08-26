/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SupportedSymmetricEnergy

/-!
# The supported gcd--singular kernel

After sorting the cofactor pair, every B5 fiber weight is a fixed analytic
factor times one purely arithmetic kernel.  The kernel is supported only on
nonempty fibers and consists of the gcd-over-product scale times the
determinant singular factor.
-/

namespace Erdos822

/-- Pair-dependent arithmetic kernel remaining after the B5 and Mertens
factors are removed. -/
noncomputable def supportedGcdSingularKernel
    (x m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs x m m').Nonempty then
    (1 + ((x * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
        ((m * m' : ℕ) : ℝ)) *
      Erdos851.singularFactor (reducedTotientDet m m') z y
  else 0

theorem supportedGcdSingularKernel_nonneg
    (x m m' z y : ℕ) :
    0 ≤ supportedGcdSingularKernel x m m' z y := by
  unfold supportedGcdSingularKernel
  split_ifs
  · exact mul_nonneg (by positivity) (singularFactor_nonneg _ _ _)
  · exact le_rfl

/-- Every supported B5 weight is bounded by a universal analytic factor
times the supported gcd--singular kernel. -/
theorem supportedSymmetricB5Weight_le_factor_mul_supportedGcdKernel
    {A C C₀ : ℝ} {x m m' z y S : ℕ}
    (hA : 0 ≤ A) (hm : 0 < m) (hm' : 0 < m') :
    supportedSymmetricB5Weight A C C₀ x m m' z y S ≤
      ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
        (C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          Real.exp (12 * C₀))) *
        supportedGcdSingularKernel x m m' z y := by
  unfold supportedSymmetricB5Weight supportedGcdSingularKernel
  by_cases hne : (outerCollisionPairs x m m').Nonempty
  · rw [if_pos hne, if_pos hne]
    have h :=
      symmetricB5SingularMainWeight_le_gcdKernel
        (A := A) (C := C) (C₀ := C₀)
        (x := x) (m := m) (m' := m') (z := z) (y := y) (S := S)
        hA hm hm'
    calc
      symmetricB5SingularMainWeight A C C₀ x m m' z y S ≤
          (1 + ((x * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
              ((m * m' : ℕ) : ℝ)) *
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
                (Erdos851.singularFactor (reducedTotientDet m m') z y *
                  Real.exp (12 * C₀)))) := h
      _ = ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
              Real.exp (12 * C₀))) *
            ((1 + ((x * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
                ((m * m' : ℕ) : ℝ)) *
              Erdos851.singularFactor (reducedTotientDet m m') z y) := by
        ring
  · rw [if_neg hne, if_neg hne]
    positivity

end Erdos822
