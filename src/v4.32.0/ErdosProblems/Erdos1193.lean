/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1193.
https://www.erdosproblems.com/forum/thread/1193

Formal authors:
- Aristotle
- Pietro Monticone

URLs:
- https://www.erdosproblems.com/forum/thread/1193#post-5360
- https://gist.githubusercontent.com/pitmonticone/c2658d464f8f5ca0e7fa40ed6fb78a5d/raw/793317d6a959dca24f5f313364c49c4c75fc5c01/Erdos1193.lean
-/
/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/
import Mathlib.Data.Finset.Card

/-!
# Erdős Problem 1193

Let `A ⊂ ℕ` and let `g(n)` be a non-decreasing function that is always positive.
Is the lower density of `{n : 1_A ∗ 1_A(n) = g(n)}` always `0`?
Is the upper density always `< c` for some constant `c < 1`?

## Answer

**No** to both questions. Taking `A = ℕ` and `g(n) = n + 1`, we have
`(1_A ∗ 1_A)(n) = n + 1 = g(n)` for all `n`, so the matching set is all of `ℕ`
and has density `1`. Presumably Erdős had additional restrictions on `g` or `A`
in mind, but these are not recorded in [Er80].

## Main results

* `conv_ind`: the additive convolution `(1_A ∗ 1_A)(n)` as a `Finset` cardinality.
* `erdos_convolution_counterexample`: `conv_ind ℕ n = n + 1` for all `n`.

## References

* P. Erdős, *A survey of problems in combinatorial number theory*,
Ann. Discrete Math. (1980), 89–115.
* [Erdős Problem #1193](https://www.erdosproblems.com/1193).
-/

open Finset Nat

namespace Erdos1193

open scoped Classical in
/-- The additive convolution of indicator functions of `A ⊆ ℕ`:
`conv_ind A n = #{k ∈ {0, …, n} | k ∈ A ∧ n - k ∈ A}`. -/
noncomputable def conv_ind (A : Set ℕ) (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun k => k ∈ A ∧ (n - k) ∈ A)).card

/-- **Erdős Problem 1193 (counterexample).** The convolution of the indicator of `ℕ` with itself
equals `n + 1` everywhere, so both the lower and upper density of the matching set are `1`.
This disproves both of Erdős's questions without additional restrictions. -/
theorem erdos_convolution_counterexample :
    ∀ n : ℕ, conv_ind Set.univ n = n + 1 := by
  simp [conv_ind]

#print axioms erdos_convolution_counterexample
-- 'Erdos1193.erdos_convolution_counterexample' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end Erdos1193
