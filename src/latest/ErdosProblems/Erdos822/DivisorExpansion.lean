/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.RoughQuadraticPrimeClasses
import ErdosProblems.Erdos822.WeightedCommonDivisorRanges

/-!
# Expanding the gcd weight over common divisors

The arithmetic kernel contains the common shifted gcd itself.  The standard
identity `∑_{d ∣ g} φ(d) = g` turns that weight into a finite sum over
moduli.  This is the correct entry point for the three-range residue
estimates, because each modulus can then be split into its smooth and rough
parts.
-/

namespace Erdos822

open scoped BigOperators

/-- One divisor summand in the supported gcd-weighted kernel. -/
noncomputable def commonDivisorKernelTerm
    (N m m' h z y : ℕ) : ℝ :=
  (((N ^ 60 : ℕ) : ℝ) * (Nat.totient h : ℝ) /
      ((m * m' : ℕ) : ℝ)) *
    Erdos851.singularFactor (reducedTotientDet m m') z y

/-- The divisor expansion of the supported weighted gcd kernel. -/
noncomputable def supportedDivisorExpandedKernel
    (N m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty then
    ∑ h ∈ (shiftedCoefficientGcd m m').divisors,
      commonDivisorKernelTerm N m m' h z y
  else 0

theorem commonDivisorKernelTerm_nonneg
    (N m m' h z y : ℕ) :
    0 ≤ commonDivisorKernelTerm N m m' h z y := by
  unfold commonDivisorKernelTerm
  exact mul_nonneg (by positivity) (singularFactor_nonneg _ _ _)

theorem supportedDivisorExpandedKernel_nonneg
    (N m m' z y : ℕ) :
    0 ≤ supportedDivisorExpandedKernel N m m' z y := by
  unfold supportedDivisorExpandedKernel
  split_ifs
  · exact Finset.sum_nonneg fun h hh =>
      commonDivisorKernelTerm_nonneg N m m' h z y
  · exact le_rfl

/-- Exact finite divisor expansion of the weighted supported kernel. -/
theorem supportedWeightedGcdSingularKernel_eq_divisorExpansion
    (N m m' z y : ℕ) :
    supportedWeightedGcdSingularKernel (N ^ 60) m m' z y =
      supportedDivisorExpandedKernel N m m' z y := by
  unfold supportedWeightedGcdSingularKernel supportedDivisorExpandedKernel
  by_cases hne : (outerCollisionPairs (N ^ 60) m m').Nonempty
  · rw [if_pos hne, if_pos hne]
    let g := shiftedCoefficientGcd m m'
    let D : ℝ := ((m * m' : ℕ) : ℝ)
    let S : ℝ := Erdos851.singularFactor (reducedTotientDet m m') z y
    have hsumNat : ∑ h ∈ g.divisors, Nat.totient h = g := by
      exact Nat.sum_totient g
    have hsumReal :
        ∑ h ∈ g.divisors, (Nat.totient h : ℝ) = (g : ℝ) := by
      exact_mod_cast hsumNat
    change (((N ^ 60 * g : ℕ) : ℝ) / D) * S =
      ∑ h ∈ g.divisors,
        ((((N ^ 60 : ℕ) : ℝ) * (Nat.totient h : ℝ) / D) * S)
    push_cast
    rw [← hsumReal, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  · rw [if_neg hne, if_neg hne]

/-- The same identity after summing over an off-diagonal cofactor family. -/
theorem sum_supportedWeightedGcdSingularKernel_eq_sum_divisorExpansion
    (B : Finset ℕ) (N z y : ℕ) :
    (∑ m ∈ B,
        ∑ m' ∈ B.erase m,
          supportedWeightedGcdSingularKernel (N ^ 60) m m' z y) =
      ∑ m ∈ B,
        ∑ m' ∈ B.erase m,
          supportedDivisorExpandedKernel N m m' z y := by
  simp_rw [supportedWeightedGcdSingularKernel_eq_divisorExpansion]

end Erdos822
