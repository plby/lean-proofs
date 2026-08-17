/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

/-!
# Erdős Problem 763

The detailed mathematical argument and its formalization plan are in
`tex/763.tex`.  We formalize the ordered additive convolution of the
indicator of an arbitrary set `A ⊆ ℕ` and prove that its summatory function
cannot differ from a positive linear function by `O(1)`.
-/

open Filter Metric Set
open scoped BigOperators Topology Asymptotics Real

namespace Erdos763

/-- The `ℕ`-valued indicator of a subset of the natural numbers. -/
noncomputable def indicator (A : Set ℕ) (n : ℕ) : ℕ :=
  open scoped Classical in
  if n ∈ A then 1 else 0

/-- The ordered representation function `(1_A * 1_A)(n)`. -/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (n + 1), indicator A a * indicator A (n - a)

/-- The summatory ordered representation function through `N`, inclusive. -/
noncomputable def summatoryRepresentationCount (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), representationCount A n

@[simp] lemma indicator_eq_one_iff {A : Set ℕ} {n : ℕ} :
    indicator A n = 1 ↔ n ∈ A := by
  classical
  simp [indicator]

@[simp] lemma indicator_le_one (A : Set ℕ) (n : ℕ) : indicator A n ≤ 1 := by
  classical
  by_cases hn : n ∈ A <;> simp [indicator, hn]

@[simp] lemma norm_indicator_cast (A : Set ℕ) (n : ℕ) :
    ‖(indicator A n : ℂ)‖ = indicator A n := by
  classical
  by_cases hn : n ∈ A <;> simp [indicator, hn]

/-! ## Bounded power series and Parseval on a circle -/

/-- The analytic function represented by a sequence of complex coefficients. -/
noncomputable def powerSeriesValue (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n * z ^ n

/-- The degree `< K` truncation of a coefficient sequence. -/
noncomputable def truncPolynomial (a : ℕ → ℂ) (r : ℝ) (K : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range K, Polynomial.monomial n (a n * (r : ℂ) ^ n)


theorem erdos_763 :
    ¬ ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
      (fun N : ℕ ↦ (summatoryRepresentationCount A N : ℝ) - c * N) =O[atTop]
        (fun _N : ℕ ↦ (1 : ℝ)) := by
  sorry

end Erdos763
