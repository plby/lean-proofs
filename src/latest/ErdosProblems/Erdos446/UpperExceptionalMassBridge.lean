/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperBlockMassError

/-!
# Erdős Problem 446: exceptional occupancy mass and prime blocks

Ford's exceptional-layer argument bounds a proper subset of a Smirnov
family much more sharply than it bounds the whole family.  In particular,
the extra `1 / (k + 1)` in equations (32h)--(33) would be lost if one first
enlarged that subset to the ambient Smirnov family.

This file records the sharp bridge needed by that argument.  Membership in
the ambient Smirnov family is used *only* to control the nonuniform Mertens
errors of the prime blocks.  The final factor is the reciprocal-factorial
mass of the original exceptional set itself.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Reciprocal-factorial mass of an arbitrary finite occupancy family. -/
noncomputable def reciprocalFactorialMassOver {v : ℕ}
    (I : Finset (Fin v → ℕ)) : ℝ :=
  ∑ b ∈ I, 1 / compositionFactorial b

theorem reciprocalFactorialMassOver_nonneg {v : ℕ}
    (I : Finset (Fin v → ℕ)) :
    0 ≤ reciprocalFactorialMassOver I := by
  apply Finset.sum_nonneg
  intro b hb
  apply one_div_nonneg.mpr
  dsimp [compositionFactorial]
  positivity

theorem reciprocalFactorialMassOver_mono {v : ℕ}
    {I J : Finset (Fin v → ℕ)} (hIJ : I ⊆ J) :
    reciprocalFactorialMassOver I ≤ reciprocalFactorialMassOver J := by
  rw [reciprocalFactorialMassOver, reciprocalFactorialMassOver]
  exact Finset.sum_le_sum_of_subset_of_nonneg hIJ fun b hbJ hbI ↦ by
    apply one_div_nonneg.mpr
    dsimp [compositionFactorial]
    positivity

/-- The sharp nonuniform prime-block estimate for a proper subset of a
Smirnov family.  Unlike `blockClusterMassOver_le_smirnovOccupancyMass`, the
right side retains the mass of `I` rather than the mass of its ambient
barrier family. -/
theorem blockClusterMassOver_le_reciprocalFactorialMass
    {M k u v : ℕ} {I : Finset (Fin v → ℕ)} {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hI : I ⊆ smirnovOccupancies k u v)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (henvelope : ∀ b ∈ I, ∀ a ∈ compositionBlockFamily M b,
      clusterLength a ≤ A) :
    blockClusterMassOver M I ≤
      A * Real.log 2 ^ k *
        Real.exp (4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M) *
          reciprocalFactorialMassOver I := by
  calc
    blockClusterMassOver M I ≤
        ∑ b ∈ I,
          A * (Real.log 2 ^ k *
            Real.exp (4 * (u + 1) * (C / Real.log 2) /
              (2 : ℝ) ^ M) /
                compositionFactorial b) := by
      apply Finset.sum_le_sum
      intro b hb
      exact compositionBlockClusterMass_le_smirnov hC hA (hI hb) hmass
        (henvelope b hb)
    _ = A * Real.log 2 ^ k *
        Real.exp (4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M) *
          reciprocalFactorialMassOver I := by
      rw [reciprocalFactorialMassOver]
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- Absolute-error-factor form.  The ambient Smirnov offset only has to be
small enough for its prefix cap to absorb the accumulated Mertens error;
the exceptional reciprocal-factorial mass is still retained exactly. -/
theorem blockClusterMassOver_le_reciprocalFactorialMass_of_offset
    {M k u v : ℕ} {I : Finset (Fin v → ℕ)} {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hu : u + 1 ≤ 2 ^ M)
    (hI : I ⊆ smirnovOccupancies k u v)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (henvelope : ∀ b ∈ I, ∀ a ∈ compositionBlockFamily M b,
      clusterLength a ≤ A) :
    blockClusterMassOver M I ≤
      A * Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
        reciprocalFactorialMassOver I := by
  have hraw := blockClusterMassOver_le_reciprocalFactorialMass
    hC hA hI hmass henvelope
  have hpow : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  have huR : ((u + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast hu
  have hratio : ((u + 1 : ℕ) : ℝ) / (2 : ℝ) ^ M ≤ 1 :=
    (div_le_one hpow).2 huR
  have hfactor : 0 ≤ 4 * C / Real.log 2 := by positivity
  have hexpArg :
      4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M ≤
        4 * C / Real.log 2 := by
    calc
      4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M =
          (4 * C / Real.log 2) *
            (((u + 1 : ℕ) : ℝ) / (2 : ℝ) ^ M) := by
        push_cast
        ring
      _ ≤ (4 * C / Real.log 2) * 1 :=
        mul_le_mul_of_nonneg_left hratio hfactor
      _ = 4 * C / Real.log 2 := by ring
  apply hraw.trans
  apply mul_le_mul_of_nonneg_right _ (reciprocalFactorialMassOver_nonneg I)
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpArg)
  positivity

end Erdos446
