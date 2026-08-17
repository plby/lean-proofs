/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import ErdosProblems.Erdos49.PNT.IEANTN.Mertens

/-!
# Erdős Problem 542

Schinzel and Szekeres proved the sharp reciprocal-sum bound `31 / 30` for
finite subsets of `[1,n]` whose distinct members have least common multiple
larger than `n`.  They also constructed admissible sets whose uncovered
multiples have density tending to zero, disproving the second assertion in
the problem.

The detailed mathematics and the correspondence with this formalization are
in `tex/542.tex`.
-/

namespace Erdos542

open Finset Filter
open scoped BigOperators ArithmeticFunction.Omega

/-- The exact LCM condition in Problem 542, including `A ⊆ {1,...,n}`. -/
def PairwiseLCMExceeds (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b

/-- The reciprocal sum, first in `ℚ` so all finite certificates are exact. -/
def reciprocalSumRat (A : Finset ℕ) : ℚ :=
  ∑ a ∈ A, (1 : ℚ) / a

/-- The real-valued reciprocal sum appearing in the problem. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (1 : ℝ) / a

/-- Integers in `[1,n]` which are not divisible by any member of `A`. -/
def uncovered (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m => ∀ a ∈ A, ¬a ∣ m

/-! ## Definitions and the Schinzel--Szekeres rational certificate -/

/-- The thirteen nonzero entries of the Schinzel--Szekeres certificate. -/
def certificate : ℕ → ℚ
  | 1 => 1
  | 2 => 1 / 2
  | 3 => 1 / 6
  | 4 => 1 / 6
  | 6 => 2 / 15
  | 10 => 31 / 420
  | 15 => 2021 / 45045
  | 16 => 2021 / 45045
  | 22 => 3565609 / 116396280
  | 28 => 148279331 / 6692786100
  | 35 => 17694671471 / 1504203675975
  | 36 => 104205434239 / 6016814703900
  | 58 => 77337724377074022791 / 13687446560419818786600
  | _ => 0

/-- Total certificate mass at ambient quotient `q`. -/
def certificateSum (q : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 q, certificate (q / k) / k

/-- The exceptional ambient values for the universal certificate. -/
def certificateExceptions : Finset ℕ := {13, 19, 20, 31, 32, 61, 62}

private lemma certificate_nonneg (j : ℕ) : 0 ≤ certificate j := by
  by_cases hj : j < 59
  · interval_cases j <;> norm_num [certificate]
  · have hj1 : j ≠ 1 := by omega
    have hj2 : j ≠ 2 := by omega
    have hj3 : j ≠ 3 := by omega
    have hj4 : j ≠ 4 := by omega
    have hj6 : j ≠ 6 := by omega
    have hj10 : j ≠ 10 := by omega
    have hj15 : j ≠ 15 := by omega
    have hj16 : j ≠ 16 := by omega
    have hj22 : j ≠ 22 := by omega
    have hj28 : j ≠ 28 := by omega
    have hj35 : j ≠ 35 := by omega
    have hj36 : j ≠ 36 := by omega
    have hj58 : j ≠ 58 := by omega
    simp [certificate, hj1, hj2, hj3, hj4, hj6, hj10, hj15, hj16,
      hj22, hj28, hj35, hj36, hj58]

end Erdos542
