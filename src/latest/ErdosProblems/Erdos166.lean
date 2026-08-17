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
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos920.Construction

/-!
# Erdős Problem 166

Mattheus and Verstraëte proved

`R(4, k) = Ω(k³ / log(k)⁴)`.

This file derives the result from the stronger general off-diagonal Ramsey
construction already formalized in `ErdosProblems.Erdos920`.  The detailed
mathematical reconstruction and the Leanization plan are in `tex/166.tex`.

References:

* S. Mattheus and J. Verstraëte, *The asymptotics of r(4,t)*,
  Ann. of Math. 199 (2024), 919–941.
* D. Bradač, *Off-diagonal Ramsey numbers*, arXiv:2605.28793 (2026).
-/

open Filter Real

syntax (name := answerSyntax166) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

/-- `g ≫ h` means that `h` is big-O of `g` at infinity. -/
notation:50 g " ≫ " h => Asymptotics.IsBigO Filter.atTop h g

namespace Erdos166

/-- The explicit Mattheus--Verstraëte lower bound
`R(4, k) = Ω(k³ / log(k)⁴)`. -/
theorem mattheus_verstraete_bound :
    (fun k : ℕ ↦ (Ramsey.ramseyNumber 4 k : ℝ)) ≫
      (fun k : ℕ ↦ (k : ℝ) ^ 3 / Real.log (k : ℝ) ^ 4) := by
  obtain ⟨A, hA, hbound⟩ :=
    Erdos920.RamseyPackaging.bradac_ramsey_lower_bound_eventually_of_dStarFamily
      2 (Erdos920.Construction.dStarFamily 2 (by omega))
  rw [Asymptotics.isBigO_iff'']
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with k hk hk2
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have htarget_nonneg :
      0 ≤ (k : ℝ) ^ 3 / Real.log (k : ℝ) ^ 4 := by positivity
  have hramsey_nonneg : 0 ≤ (Ramsey.ramseyNumber 4 k : ℝ) := by positivity
  rw [Real.norm_of_nonneg htarget_nonneg, Real.norm_of_nonneg hramsey_nonneg]
  simpa [mul_div_assoc] using hk

/-- Erdős Problem 166 has a positive answer.  The existential natural
exponent is a faithful rendering of `(log k)^{O(1)}`, and the proof supplies
the established value `4`. -/
theorem erdos_166 : answer(True) ↔
    ∃ c : ℕ, 0 < c ∧
      (fun k : ℕ ↦ (Ramsey.ramseyNumber 4 k : ℝ)) ≫
        (fun k : ℕ ↦ (k : ℝ) ^ 3 / Real.log (k : ℝ) ^ c) := by
  constructor
  · intro _
    exact ⟨4, by norm_num, mattheus_verstraete_bound⟩
  · intro _
    trivial

end Erdos166

#print axioms Erdos166.erdos_166
