/- leanprover/lean4:v4.33.0 -/
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

import ErdosProblems.Erdos721.LocalNarrowing

/-!
# Finite termination of the local density-increment iteration

This file begins the finite structural iteration used in the cyclic
Bloom--Sisask argument.  Its first lemma isolates the termination mechanism:
a state whose density is at most one cannot have a fixed multiplicative
density increment at every stage.
-/

namespace Erdos721

open Function

/-- If every nonterminal state admits a fixed multiplicative density
increment, while every state has density in `(0,1]`, then some terminal state
exists.  The proof chooses successors and iterates them; unbounded growth of
`(1 + epsilon)^n` supplies the contradiction. -/
theorem exists_terminal_of_uniform_density_increment
    {S : Type*} [Nonempty S] (terminal : S → Prop) (density : S → ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hdensity0 : ∀ s, 0 < density s)
    (hdensity1 : ∀ s, density s ≤ 1)
    (hstep : ∀ s, ¬ terminal s →
      ∃ s', (1 + epsilon) * density s ≤ density s') :
    ∃ s, terminal s := by
  by_contra hterminal
  push Not at hterminal
  have hnext (s : S) : ∃ s', (1 + epsilon) * density s ≤ density s' :=
    hstep s (hterminal s)
  let next : S → S := fun s ↦ Classical.choose (hnext s)
  have hnext_spec (s : S) :
      (1 + epsilon) * density s ≤ density (next s) :=
    Classical.choose_spec (hnext s)
  let s0 : S := Classical.choice inferInstance
  have hiter (n : ℕ) :
      (1 + epsilon) ^ n * density s0 ≤ density ((next^[n]) s0) := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          (1 + epsilon) ^ (n + 1) * density s0 =
              (1 + epsilon) * ((1 + epsilon) ^ n * density s0) := by ring
          _ ≤ (1 + epsilon) * density ((next^[n]) s0) :=
            mul_le_mul_of_nonneg_left ih (by linarith)
          _ ≤ density (next ((next^[n]) s0)) := hnext_spec _
          _ = density ((next^[n + 1]) s0) := by
            rw [Function.iterate_succ_apply']
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (density s0)⁻¹ (by linarith : 1 < 1 + epsilon)
  have hbig : 1 < (1 + epsilon) ^ n * density s0 := by
    rwa [inv_lt_iff_one_lt_mul₀ (hdensity0 s0)] at hn
  exact (not_lt_of_ge ((hiter n).trans (hdensity1 _))) hbig

end Erdos721
