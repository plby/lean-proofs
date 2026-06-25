/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 692.
https://www.erdosproblems.com/forum/thread/692

Informal authors:
- Stijn Cambie

Formal authors:
- Aristotle
- Pietro Monticone

URLs:
- https://www.erdosproblems.com/forum/thread/692#post-5204
- https://gist.githubusercontent.com/pitmonticone/96516af9100a37a1da81908dc0b0410c/raw/a1d6ca7f3835c58b257e5e715c8fdf3a224e1bd0/Erdos692.lean
-/
/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Erdős Problem 692

Let `δ₁(n, m)` be the natural density of the set of integers with exactly one
divisor in `(n, m)`. Is `δ₁(n, m)` unimodal for `m > n + 1`?

## Answer

No. Cambie shows that `δ₁(3, 7) < δ₁(3, 6)` and `δ₁(3, 7) < δ₁(3, 8)`, so
the sequence `(δ₁(3, m))_{m ≥ 5}` has a local minimum at `m = 7`, violating
unimodality. More precisely:
- `δ₁(3, 6) = 7/20`
- `δ₁(3, 7) = 1/3`
- `δ₁(3, 8) = 38/105`

and `1/3 < 7/20 < 38/105`.

## References

* S. Cambie, *Resolution of Erdős' problems about unimodularity*,
  [arXiv:2501.10333](https://arxiv.org/abs/2501.10333) (2025).
* [Erdős Problem #692](https://www.erdosproblems.com/692).
-/

namespace Erdos692

open Finset

/-! ### Counting functions -/

/-- The number of divisors of `x` that lie in the open interval `(n, m)`. -/
def numDivisorsIn (x n m : ℕ) : ℕ :=
  ((Ioo n m).filter (· ∣ x)).card

/-- The count of integers in `{1, …, L}` having exactly one divisor in `(n, m)`. -/
def countWithOneDivisor (n m L : ℕ) : ℕ :=
  ((Icc 1 L).filter (numDivisorsIn · n m = 1)).card

/-! ### Periodicity -/

/-- The predicate `d ∣ x` is periodic in `x` with period `L = lcm{n+1, …, m−1}`
for every `d ∈ (n, m)`, since each such `d` divides `L`. Therefore the count
of divisors in `(n, m)` is also periodic. -/
theorem numDivisorsIn_periodic (x n m : ℕ) :
    numDivisorsIn (x + (Ioo n m).lcm id) n m = numDivisorsIn x n m := by
  simp only [numDivisorsIn]
  congr 1
  refine filter_congr fun d hd => ?_
  rw [add_comm]
  exact Nat.dvd_add_right <| dvd_lcm hd

/-! ### The density function `δ₁`

By `numDivisorsIn_periodic`, the predicate `numDivisorsIn x n m = 1` is periodic
with period `L = lcm{n+1, …, m−1}`. The natural density therefore exists and
equals the proportion of residues in `{1, …, L}` satisfying the predicate. -/

/-- The density `δ₁(n, m)` of integers with exactly one divisor in `(n, m)`,
computed as the proportion of residues modulo `L = lcm{n+1, …, m−1}` that
have exactly one such divisor. -/
noncomputable def delta1 (n m : ℕ) : ℚ :=
  countWithOneDivisor n m ((Ioo n m).lcm id) / ((Ioo n m).lcm id)

/-! ### Concrete lcm and count computations -/

theorem lcm_Ioo_3_6 : (Ioo 3 6).lcm id = 20 := by
  decide

theorem lcm_Ioo_3_7 : (Ioo 3 7).lcm id = 60 := by
  decide

theorem lcm_Ioo_3_8 : (Ioo 3 8).lcm id = 420 := by
  decide

theorem count_3_6 : countWithOneDivisor 3 6 20 = 7 := by
  decide

theorem count_3_7 : countWithOneDivisor 3 7 60 = 20 := by
  decide

set_option maxRecDepth 680 in
theorem count_3_8 : countWithOneDivisor 3 8 420 = 152 := by
  decide

/-! ### Concrete values of `δ₁` -/

/-- `δ₁(3, 6) = 7/20`. -/
theorem delta1_3_6 : delta1 3 6 = 7 / 20 := by
  norm_num [delta1, lcm_Ioo_3_6, count_3_6]

/-- `δ₁(3, 7) = 1/3`. -/
theorem delta1_3_7 : delta1 3 7 = 1 / 3 := by
  norm_num [delta1, lcm_Ioo_3_7, count_3_7]

/-- `δ₁(3, 8) = 38/105`. -/
theorem delta1_3_8 : delta1 3 8 = 38 / 105 := by
  norm_num [delta1, lcm_Ioo_3_8, count_3_8]

/-! ### Non-unimodality -/

/-- `δ₁(3, 7) < δ₁(3, 6)`. -/
theorem delta1_3_7_lt_3_6 : delta1 3 7 < delta1 3 6 := by
  norm_num [delta1_3_7, delta1_3_6]

/-- `δ₁(3, 7) < δ₁(3, 8)`. -/
theorem delta1_3_7_lt_3_8 : delta1 3 7 < delta1 3 8 := by
  norm_num [delta1_3_7, delta1_3_8]

/-- **Erdős Problem 692** (Cambie 2025): The sequence `m ↦ δ₁(3, m)` is **not** unimodal.

It has a local minimum at `m = 7`: `δ₁(3, 7) = 1/3 < 7/20 = δ₁(3, 6)` and
`δ₁(3, 7) = 1/3 < 38/105 = δ₁(3, 8)`. -/
theorem delta1_not_unimodal :
    delta1 3 7 < delta1 3 6 ∧ delta1 3 7 < delta1 3 8 :=
  ⟨delta1_3_7_lt_3_6, delta1_3_7_lt_3_8⟩

#print axioms delta1_not_unimodal
-- 'Erdos692.delta1_not_unimodal' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos692
