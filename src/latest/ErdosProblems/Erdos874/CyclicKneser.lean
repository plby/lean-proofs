/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
import ErdosProblems.Erdos13.Erdos13Kneser

/-!
# Kneser's theorem for cyclic sumsets

This file exposes the kernel-checked Kneser theorem proved in
`ErdosProblems.Erdos13.Erdos13Kneser` in the forms used by the additive
combinatorics development for Erdős Problem 874.

For a finite sumset `A + B`, `Finset.addStab` is its finite translation
stabilizer.  The first theorem below is Kneser's subtraction-free inequality;
the following two theorems give the familiar natural- and integer-valued
forms

`|A + B| ≥ |A + H| + |B + H| - |H|`.

The theorem is valid in every additive commutative group.  The final wrappers
specialize it to the finite cyclic group `ZMod n`.
-/

open scoped Pointwise

namespace Erdos874

section AddCommGroup

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- For a nonempty sumset, `Finset.addStab` is exactly the usual additive
translation stabilizer, represented as a finite set. -/
theorem coe_sum_addStab_eq_stabilizer (A B : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ((A + B).addStab : Set G) =
      (AddAction.stabilizer G ((A + B : Finset G) : Set G) : Set G) := by
  exact Finset.coe_addStab (hA.add hB)

/-- Kneser's addition theorem, in a subtraction-free form convenient over
natural-number cardinalities.  Here `H = (A + B).addStab` is the translation
stabilizer of the sumset. -/
theorem add_kneser_subtraction_free (A B : Finset G) :
    (A + (A + B).addStab).card + (B + (A + B).addStab).card ≤
      (A + B).card + (A + B).addStab.card := by
  exact Finset.add_kneser A B

/-- Kneser's addition theorem with truncated subtraction in `ℕ`. -/
theorem add_kneser_tsub (A B : Finset G) :
    (A + (A + B).addStab).card + (B + (A + B).addStab).card -
        (A + B).addStab.card ≤
      (A + B).card := by
  have h := add_kneser_subtraction_free A B
  omega

/-- Kneser's addition theorem in `ℤ`; this is the literal cardinality
inequality `|A+B| ≥ |A+H|+|B+H|-|H|`. -/
theorem add_kneser_int (A B : Finset G) :
    ((A + (A + B).addStab).card : ℤ) +
          ((B + (A + B).addStab).card : ℤ) -
        ((A + B).addStab.card : ℤ) ≤
      ((A + B).card : ℤ) := by
  have h := add_kneser_subtraction_free A B
  omega

/-- If the Kneser inequality cannot fall into its strict alternative, then it
is an equality.  The hypothesis is a convenient way of excluding the strict
alternative furnished by `Finset.add_strict_kneser`. -/
theorem add_kneser_eq_of_sum_card_lt_saturations (A B : Finset G)
    (hcard : (A + B).card <
      (A + (A + B).addStab).card + (B + (A + B).addStab).card) :
    (A + (A + B).addStab).card + (B + (A + B).addStab).card =
      (A + B).card + (A + B).addStab.card := by
  apply Nat.le_antisymm (add_kneser_subtraction_free A B)
  by_contra hnot
  have hstrict :
      (A + (A + B).addStab).card + (B + (A + B).addStab).card <
        (A + B).card + (A + B).addStab.card := by
    omega
  have hsmall := Finset.add_strict_kneser A B hstrict
  omega

end AddCommGroup

section Cyclic

variable {n : ℕ}

/-- Kneser's theorem for two finite subsets of the cyclic group `ZMod n`. -/
theorem zmod_kneser (A B : Finset (ZMod n)) :
    (A + (A + B).addStab).card + (B + (A + B).addStab).card ≤
      (A + B).card + (A + B).addStab.card :=
  add_kneser_subtraction_free A B

/-- The usual natural-number form of Kneser's theorem in `ZMod n`. -/
theorem zmod_kneser_tsub (A B : Finset (ZMod n)) :
    (A + (A + B).addStab).card + (B + (A + B).addStab).card -
        (A + B).addStab.card ≤
      (A + B).card :=
  add_kneser_tsub A B

/-- The usual integer-cardinality form of Kneser's theorem in `ZMod n`. -/
theorem zmod_kneser_int (A B : Finset (ZMod n)) :
    ((A + (A + B).addStab).card : ℤ) +
          ((B + (A + B).addStab).card : ℤ) -
        ((A + B).addStab.card : ℤ) ≤
      ((A + B).card : ℤ) :=
  add_kneser_int A B

/-- Self-sum specialization of Kneser's theorem in `ZMod n`. -/
theorem zmod_self_kneser (A : Finset (ZMod n)) :
    2 * (A + (A + A).addStab).card ≤
      (A + A).card + (A + A).addStab.card := by
  simpa [two_mul] using zmod_kneser A A

/-- Both the self-sum and the stabilizer-saturation of `A` have cardinality
divisible by the size of the self-sum stabilizer. -/
theorem zmod_self_kneser_divisibilities (A : Finset (ZMod n)) :
    (A + A).addStab.card ∣ (A + (A + A).addStab).card ∧
      (A + A).addStab.card ∣ (A + A).card := by
  exact ⟨Finset.card_addStab_dvd_card_add_addStab A (A + A),
    Finset.card_addStab_dvd_card (A + A)⟩

/-- Equality in self-sum Kneser when the strict Kneser alternative would be
incompatible with the size of the self-sum. -/
theorem zmod_self_kneser_eq_of_sum_card_lt_saturation (A : Finset (ZMod n))
    (hcard : (A + A).card < 2 * (A + (A + A).addStab).card) :
    2 * (A + (A + A).addStab).card =
      (A + A).card + (A + A).addStab.card := by
  simpa [two_mul] using
    add_kneser_eq_of_sum_card_lt_saturations A A (by simpa [two_mul] using hcard)

end Cyclic

end Erdos874
