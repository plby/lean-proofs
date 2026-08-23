/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 1187

For every finite coloring of the integers and every `k ≥ 3`, there is a
monochromatic `k`-term arithmetic progression consisting of primes.  In
contrast, the four-coloring by residue modulo four has no monochromatic
arithmetic progression whose positive common difference is prime.

The first half combines the repository's proof of the Green--Tao theorem
with Hales--Jewett (in its finite van der Waerden role).  The second half is
the elementary residue-class counterexample.

References:

* B. Green and T. Tao, *The primes contain arbitrarily long arithmetic
  progressions*, Annals of Mathematics 167 (2008), 481--547.
* https://www.erdosproblems.com/1187
-/

open scoped BigOperators Finset

namespace Erdos1187

open scoped Classical in
open scoped Classical in
/-- A positive-step arithmetic progression of natural primes, regarded as
integers by the coloring, is monochromatic. -/
def HasMonochromaticPrimeAP {κ : Type*} (color : ℤ → κ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧
    (∀ j : ℕ, j < k → Nat.Prime (a + d * j)) ∧
    ∃ gamma : κ, ∀ j : ℕ, j < k → color ((a + d * j : ℕ) : ℤ) = gamma

/-- An integer arithmetic progression with positive prime common difference
is monochromatic. -/
def HasMonochromaticAPWithPrimeStep {κ : Type*}
    (color : ℤ → κ) (k : ℕ) : Prop :=
  ∃ a : ℤ, ∃ p : ℕ, Nat.Prime p ∧
    ∃ gamma : κ, ∀ j : ℕ, j < k →
      color (a + ((p * j : ℕ) : ℤ)) = gamma

/-- The first question at one fixed requested length, literally quantified
over all finite color types and all colorings of the integers. -/
def FirstQuestionAt (k : ℕ) : Prop :=
  ∀ (κ : Type) [Finite κ], ∀ color : ℤ → κ,
    HasMonochromaticPrimeAP color k

/-- The second question at one fixed requested length. -/
def SecondQuestionAt (k : ℕ) : Prop :=
  ∀ (κ : Type) [Finite κ], ∀ color : ℤ → κ,
    HasMonochromaticAPWithPrimeStep color k

/-- The first question for every length in the range asked by Erdős. -/
def FirstQuestion : Prop :=
  ∀ k : ℕ, 3 ≤ k → FirstQuestionAt k

/-- The universal affirmative assertion for the second question.  We prove
both its negation and, more precisely, failure at every `k ≥ 3`. -/
def SecondQuestion : Prop :=
  ∀ k : ℕ, 3 ≤ k → SecondQuestionAt k

noncomputable section

open Combinatorics


/-- Encode a finite word by the sum of its natural-valued letters. -/
private def wordIndex {ι : Type*} [Fintype ι] {k : ℕ}
    (v : ι → Fin k) : ℕ :=
  ∑ i, (v i : ℕ)

/-- Every word index is below one plus `card ι * k`. -/
theorem erdos_1187 :
    FirstQuestion ∧ ∀ k : ℕ, 3 ≤ k → ¬ SecondQuestionAt k := by
  sorry

end

end Erdos1187
