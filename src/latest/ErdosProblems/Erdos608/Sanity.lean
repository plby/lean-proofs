/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file has been modified for Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 608.
Informal authors: Zoltán Füredi, Zeinab Maleki; construction described by
Andrzej Grzesik, Ping Hu, and Jan Volec.
Formal authors: Claude Fable 5, Emerson Hsieh.
Source: https://github.com/teorth/erdosproblems/pull/365
https://github.com/primateria/erdos608/tree/b50849234b8de6cb5c642b5cb0479cab2e9e9908
Original Lean version: 4.27.0.
Original Mathlib revision: a3a10db0e9d66acbebf76c5e6a135066525ac900 (v4.27.0).
-/
import ErdosProblems.Erdos608.Statement

set_option linter.mathlibStandardSet false

/-
Sanity check for the Erdős 608 statement file.

This module proves that the word-for-word `∀ n` reading of the problem is
degenerately FALSE, which is exactly why `Erdos608.Conjecture` in
`Erdos608/Statement.lean` is phrased in the eventually-form
(`∃ n₀, ∀ n ≥ n₀, …`).
-/

namespace Erdos608

/-- The literal, non-asymptotic reading of Erdős 608 — "for **all** `n`, every
`n`-vertex graph with more than `n²/4` edges has at least `(2/9)n²` pentagonal
edges" — is false for a degenerate reason: at `n = 3` the complete graph `K₃`
has `3 > 9/4` edges, yet no pentagon can exist on only three vertices, so it
has zero pentagonal edges and `2·3² ≤ 9·0` fails.

This lemma documents WHY the approved statement (`Erdos608.Conjecture`) uses
the eventually-form `∃ n₀, ∀ n, n₀ ≤ n → …`: under the literal `∀ n` form, a
two-line degenerate counterexample like this one would "disprove" the problem
while saying nothing about the Füredi–Maleki construction that the site's
DISPROVED verdict actually refers to. -/
theorem literal_form_false :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        n ^ 2 < 4 * G.edgeSet.ncard → 2 * n ^ 2 ≤ 9 * (Erdos608.pentEdges G).ncard := by
  intro h
  -- `K₃` (the complete graph on `Fin 3`) has exactly 3 edges.
  have hcard : (⊤ : SimpleGraph (Fin 3)).edgeSet.ncard = 3 := by
    rw [Set.ncard_eq_toFinset_card']
    decide
  -- `K₃` has no pentagonal edges: a pentagon needs five pairwise-distinct
  -- vertices, which cannot exist in `Fin 3`.
  have hpent : Erdos608.pentEdges (⊤ : SimpleGraph (Fin 3)) = ∅ := by
    ext e
    simp only [Erdos608.pentEdges, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hc5
    obtain ⟨a, b, c, d, f, hab, hac, had, haf, hbc, hbd, hbf, hcd, hcf, hdf, -⟩ := hc5
    have h5 : ({a, b, c, d, f} : Finset (Fin 3)).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, haf]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd, hbf]),
        Finset.card_insert_of_notMem (by simp [hcd, hcf]),
        Finset.card_insert_of_notMem (by simp [hdf]), Finset.card_singleton]
    have hle : ({a, b, c, d, f} : Finset (Fin 3)).card ≤ Fintype.card (Fin 3) :=
      Finset.card_le_univ _
    rw [h5, Fintype.card_fin] at hle
    omega
  -- The hypothesis holds at `n = 3`, `G = K₃`: `9 < 4 · 3 = 12` …
  have h3 := h 3 ⊤ (by rw [hcard]; norm_num)
  -- … but the conclusion `18 ≤ 9 · 0` does not.
  rw [hpent, Set.ncard_empty] at h3
  omega

end Erdos608
