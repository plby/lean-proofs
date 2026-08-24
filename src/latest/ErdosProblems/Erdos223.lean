/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 223.
https://www.erdosproblems.com/forum/thread/223

Informal authors:
- Konrad J. Swanepoel

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos223.md
-/
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

import ErdosProblems.Erdos223.Asymptotic
import ErdosProblems.Erdos223.Exact
import ErdosProblems.Erdos223.Plane
import ErdosProblems.Erdos223.Space

/-!
# Erdős Problem 223

The mathematical proof and the correspondence between its lemmas and this
formal development are documented in `tex/223.tex`.

For a finite set of `n` points in Euclidean `d`-space whose metric diameter
is one, `Erdos223.f d n` is the maximum number of unordered pairs at distance
one.  The proposition below records the complete source-verified resolution:
the small-cardinality exceptions, the high-dimensional limit, the repaired
eventual exact branches, and the infinite seven-dimensional counterexample to
Swanepoel's published universal exact claim.
-/

open Filter

namespace Erdos223

/-- Swanepoel's published universal eventual-exact claim, expressed using
`exactValue`.  The seven-dimensional construction below refutes this
proposition. -/
def PublishedEventualExactClaim : Prop :=
  ∀ d, 4 ≤ d → ∃ N, ∀ n, N ≤ n → f d n = exactValue d n

/-- The complete, source-corrected resolution of Erdős Problem 223.  Besides
the exact low-dimensional answers and Erdős's asymptotic estimate, it records
the exact branches established by the carrier argument and the failure of the
published universal exact formula. -/
def Resolution : Prop :=
  f 2 2 = 1 ∧
  (∀ n, 3 ≤ n → f 2 n = n) ∧
  f 3 2 = 1 ∧
  f 3 3 = 3 ∧
  (∀ n, 4 ≤ n → f 3 n = 2 * n - 2) ∧
  (∀ d, 4 ≤ d →
    Tendsto (fun n : ℕ ↦ (f d n : ℝ) / (n : ℝ) ^ 2) atTop
      (nhds ((((d / 2 : ℕ) : ℝ) - 1) / (2 * (d / 2 : ℕ))))) ∧
  (∃ N, ∀ n, N ≤ n → f 4 n = exactValue 4 n) ∧
  (∀ d, 6 ≤ d → Even d →
    ∃ N, ∀ n, N ≤ n → f d n = exactValue d n) ∧
  ¬ PublishedEventualExactClaim ∧
  (∀ N, ∃ n, N ≤ n ∧ exactValue 7 n < f 7 n)

/-- Swanepoel's universal eventual-exact formula is false: dimension seven
has counterexamples beyond every proposed threshold. -/
theorem not_publishedEventualExactClaim : ¬ PublishedEventualExactClaim := by
  intro h
  obtain ⟨N, hN⟩ := h 7 (by omega)
  obtain ⟨n, hn, hlt⟩ := infinitely_often_exactValue_seven_lt_f N
  exact hlt.ne (hN n hn).symm

/-- The source-corrected resolution of Erdős Problem 223. -/
theorem erdos_223 :
    f 2 2 = 1 ∧
    (∀ n, 3 ≤ n → f 2 n = n) ∧
    f 3 2 = 1 ∧
    f 3 3 = 3 ∧
    (∀ n, 4 ≤ n → f 3 n = 2 * n - 2) ∧
    (∀ d, 4 ≤ d →
      Tendsto (fun n : ℕ ↦ (f d n : ℝ) / (n : ℝ) ^ 2) atTop
        (nhds ((((d / 2 : ℕ) : ℝ) - 1) / (2 * (d / 2 : ℕ))))) ∧
    (∃ N, ∀ n, N ≤ n → f 4 n = exactValue 4 n) ∧
    (∀ d, 6 ≤ d → Even d →
      ∃ N, ∀ n, N ≤ n → f d n = exactValue d n) ∧
    ¬ (∀ d, 4 ≤ d → ∃ N, ∀ n, N ≤ n → f d n = exactValue d n) ∧
    (∀ N, ∃ n, N ≤ n ∧ exactValue 7 n < f 7 n) := by
  refine ⟨f_two 2 (by omega), ?_, f_two 3 (by omega), f_space_three,
    f_space, ?_, eventually_f_eq_exactValue_four, ?_,
    not_publishedEventualExactClaim, infinitely_often_exactValue_seven_lt_f⟩
  · exact fun n hn ↦ f_plane n hn
  · exact fun d hd ↦ f_ratio_tendsto d hd
  · exact fun d hd heven ↦ eventually_f_eq_exactValue_of_even hd heven

end Erdos223

#print axioms Erdos223.erdos_223
