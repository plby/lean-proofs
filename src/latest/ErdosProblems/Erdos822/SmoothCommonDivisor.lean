/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.DivisorExpansion

/-!
# Smooth classes and the rough common divisor

The paper does not sum over the smooth prime powers inside a common
coefficient.  It first fixes the smooth part d of every shifted
coefficient.  Inside one such class the common coefficient gcd is exactly
d times its rough part, so the totient divisor expansion only has to run
over rough divisors.
-/

namespace Erdos822

open scoped BigOperators

/-- Cofactors in B whose shifted coefficient has prescribed smooth part. -/
def shiftedSmoothClass (B : Finset ℕ) (y d : ℕ) : Finset ℕ :=
  B.filter fun m => smoothPart (shiftedTotient m) y = d

@[simp]
theorem mem_shiftedSmoothClass_iff
    {B : Finset ℕ} {y d m : ℕ} :
    m ∈ shiftedSmoothClass B y d ↔
      m ∈ B ∧ smoothPart (shiftedTotient m) y = d := by
  simp [shiftedSmoothClass]

/-- Equal smooth parts pass to the gcd. -/
theorem smoothPart_gcd_eq_of_eq
    {a b y d : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : smoothPart a y = d) (hb : smoothPart b y = d) :
    smoothPart (Nat.gcd a b) y = d := by
  have hd0 : d ≠ 0 := by
    rw [← ha]
    exact smoothPart_ne_zero a y
  apply Nat.eq_of_factorization_eq'
    (smoothPart_ne_zero (Nat.gcd a b) y) hd0
  rw [factorization_smoothPart]
  unfold smoothFactorization
  rw [Nat.factorization_gcd ha0 hb0]
  have had : smoothFactorization a y = d.factorization := by
    rw [← ha, factorization_smoothPart]
  have hbd : smoothFactorization b y = d.factorization := by
    rw [← hb, factorization_smoothPart]
  ext p
  by_cases hpy : p ≤ y
  · have hab : a.factorization p = b.factorization p := by
      have hfun :
          smoothFactorization a y p = smoothFactorization b y p := by
        rw [had, hbd]
      simpa [smoothFactorization, hpy] using hfun
    have hbdp : b.factorization p = d.factorization p := by
      have hfun := DFunLike.congr_fun hbd p
      simpa [smoothFactorization, hpy] using hfun
    simp [hpy, hab, hbdp]
  · have hbdp : 0 = d.factorization p := by
      have hfun := DFunLike.congr_fun hbd p
      simpa [smoothFactorization, hpy] using hfun
    simp [hpy, hbdp]

/-- In one shifted-smooth class the full common coefficient gcd is the
fixed smooth part times its rough part. -/
theorem shiftedCoefficientGcd_eq_smooth_mul_rough_of_class
    {m m' y d : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hmd : smoothPart (shiftedTotient m) y = d)
    (hm'd : smoothPart (shiftedTotient m') y = d) :
    shiftedCoefficientGcd m m' =
      d * roughPart (shiftedCoefficientGcd m m') y := by
  have hm0 : shiftedTotient m ≠ 0 := by
    exact (hm.trans_le (Nat.le_add_right m (Nat.totient m))).ne'
  have hm'0 : shiftedTotient m' ≠ 0 := by
    exact (hm'.trans_le (Nat.le_add_right m' (Nat.totient m'))).ne'
  have hg0 : shiftedCoefficientGcd m m' ≠ 0 := by
    unfold shiftedCoefficientGcd
    exact Nat.gcd_ne_zero_right hm'0
  have hsmooth :
      smoothPart (shiftedCoefficientGcd m m') y = d := by
    unfold shiftedCoefficientGcd
    exact smoothPart_gcd_eq_of_eq hm0 hm'0 hmd hm'd
  calc
    shiftedCoefficientGcd m m' =
        smoothPart (shiftedCoefficientGcd m m') y *
          roughPart (shiftedCoefficientGcd m m') y := by
      symm
      exact smoothPart_mul_roughPart hg0
    _ = d * roughPart (shiftedCoefficientGcd m m') y := by
      rw [hsmooth]

/-- Divisor expansion after the fixed smooth factor has been pulled out. -/
noncomputable def smoothClassRoughDivisorExpandedKernel
    (N d m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty then
    ∑ h ∈ (roughPart (shiftedCoefficientGcd m m') y).divisors,
      (((N ^ 60 * (d * Nat.totient h) : ℕ) : ℝ) /
          ((m * m' : ℕ) : ℝ)) *
        Erdos851.singularFactor (reducedTotientDet m m') z y
  else 0

/-- On a fixed shifted-smooth class, the supported weighted kernel is
exactly the rough divisor expansion. -/
theorem supportedWeightedGcdSingularKernel_eq_smoothClassRoughExpansion
    {N d m m' z y : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hmd : smoothPart (shiftedTotient m) y = d)
    (hm'd : smoothPart (shiftedTotient m') y = d) :
    supportedWeightedGcdSingularKernel (N ^ 60) m m' z y =
      smoothClassRoughDivisorExpandedKernel N d m m' z y := by
  unfold supportedWeightedGcdSingularKernel
    smoothClassRoughDivisorExpandedKernel
  by_cases hne : (outerCollisionPairs (N ^ 60) m m').Nonempty
  · rw [if_pos hne, if_pos hne]
    let g := roughPart (shiftedCoefficientGcd m m') y
    let D : ℝ := ((m * m' : ℕ) : ℝ)
    let S : ℝ := Erdos851.singularFactor (reducedTotientDet m m') z y
    have hsumNat : ∑ h ∈ g.divisors, Nat.totient h = g := by
      exact Nat.sum_totient g
    have hsumReal :
        ∑ h ∈ g.divisors, (Nat.totient h : ℝ) = (g : ℝ) := by
      exact_mod_cast hsumNat
    have hg :
        shiftedCoefficientGcd m m' = d * g := by
      simpa [g] using
        shiftedCoefficientGcd_eq_smooth_mul_rough_of_class
          hm hm' hmd hm'd
    change (((N ^ 60 * shiftedCoefficientGcd m m' : ℕ) : ℝ) / D) * S =
      ∑ h ∈ g.divisors,
        ((((N ^ 60 * (d * Nat.totient h) : ℕ) : ℝ) / D) * S)
    rw [hg]
    push_cast
    rw [← hsumReal, Finset.mul_sum]
    rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  · rw [if_neg hne, if_neg hne]

end Erdos822
