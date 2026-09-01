/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1099.
https://www.erdosproblems.com/forum/thread/1099

Informal authors:
- Michael D. Vose

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1099.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import ErdosProblems.Erdos1099.Basic
import ErdosProblems.Erdos1099.Construction
import ErdosProblems.Erdos1099.Shell

/-!
# Erdős Problem 1099

Let the positive divisors of `n` be

`1 = d₁ < d₂ < ... < d_{τ(n)} = n`.

For `α > 1`, Erdős asked whether the liminf of

`∑ i, (d_{i+1} / d_i - 1) ^ α`

is bounded by a constant depending only on `α`.  Vose proved that the answer
is yes.  The proof formalized here constructs the explicit cofinal sequence

`2 ^ (1 + ... + k) * ∏ i ∈ Icc 1 k, (2 ^ i + 1)`.

The finite divisor chains constructed in `Erdos1099.Shell` have uniformly
bounded relative-gap energy.  The refinement theorem shows that inserting all
the remaining divisors can only decrease this energy.

The theorem below includes frequent boundedness along `atTop`.  This is the
substantive, non-vacuous interpretation of the question; the literal
real-valued liminf inequality is included as the final conjunct.

See `tex/1099.tex` for the complete mathematical proof and source discussion.
-/

open Filter

namespace Erdos1099

noncomputable section

/-- **Erdős Problem 1099 (Vose, affirmative).**  For every real `α > 1`, the
power energy of consecutive relative divisor gaps is bounded on a cofinal set
of positive integers.  In particular, its liminf is finite. -/
theorem erdos_1099 (α : ℝ) (hα : 1 < α) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∃ᶠ n : ℕ in atTop, hAlpha α n ≤ C) ∧
      Filter.liminf (hAlpha α) atTop ≤ C := by
  let C := globalRelativeBound α
  have hC : 0 ≤ C := by
    simpa [C] using (globalRelativeBound_nonneg : 0 ≤ globalRelativeBound α)
  have hu : Tendsto (fun k : ℕ ↦ voseNumber (k + 3)) atTop atTop :=
    voseNumber_tendsto_atTop.comp (tendsto_add_atTop_nat 3)
  have hbound : ∀ k : ℕ, hAlpha α (voseNumber (k + 3)) ≤ C := by
    intro k
    simpa [C] using
      hAlpha_voseNumber_le_globalRelativeBound hα (by omega : 3 ≤ k + 3)
  have hfreq : ∃ᶠ n : ℕ in atTop, hAlpha α n ≤ C :=
    frequently_le_of_cofinal_sequence hu hbound
  exact ⟨C, hC, hfreq, liminf_le_of_frequently_hAlpha_le hfreq⟩

end

end Erdos1099

#print axioms Erdos1099.erdos_1099
