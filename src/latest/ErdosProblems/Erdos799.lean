/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 799.
https://www.erdosproblems.com/forum/thread/799

Informal authors:
- Noga Alon
- Michael Krivelevich
- Benny Sudakov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos799.md
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos799.Asymptotic
import ErdosProblems.Erdos799.Density
import ErdosProblems.Erdos799.HeavyColor
import ErdosProblems.Erdos799.Ramsey

/-!
# Erdős Problem 799

The list chromatic number `χ_L(G)` is the least `k` such that every assignment
of a `k`-element colour list to each vertex admits a proper colouring chosen
from those lists.  Erdős, Rubin, and Taylor asked whether `χ_L(G) = o(n)` for
almost all labelled graphs on `n` vertices.

The answer is yes.  The formal statement below exhibits a deterministic
sublinear function `b` such that the proportion of graphs on `Fin n` with
`χ_L(G) ≤ b n` tends to one.  The proof combines:

* the logarithmic upper tail for the clique number of `G(n, 1/2)`;
* finite Ramsey's theorem; and
* a heavy-colour packing argument followed by Hall's theorem.

Alon originally proved the stronger bound
`O(n * log (log n) / log n)`, and Alon--Krivelevich--Sudakov later proved the
sharp order `Θ(n / log n)`.  The Ramsey argument here is a shorter proof of
the exact affirmative assertion of Problem 799.
-/

namespace Erdos799

open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- The exact assertion that the list chromatic number is sublinear for
almost all labelled graphs.  The denominator in `graphDensity` is
`Fintype.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2`, so the second conjunct
is precisely an almost-everywhere statement for `G(n, 1/2)`. -/
def AlmostAllListChromaticSublinear : Prop :=
  ∃ b : ℕ → ℕ,
    (fun n : ℕ ↦ (b n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) ∧
    Tendsto
      (graphDensity
        (fun n G ↦ Erdos753.listChromaticNumber G ≤ b n))
      atTop (nhds 1)

/-- A graph with no clique of order `Erdos1037.r_val n` has list chromatic
number at most the diagonal Ramsey bound. -/
lemma listChromaticNumber_le_ramseyDiagonalBound
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hclique : G.cliqueNum < Erdos1037.r_val n) :
    Erdos753.listChromaticNumber G ≤ ramseyDiagonalBound n := by
  have hnonempty :
      {b : ℕ | ∃ q : ℕ, 0 < q ∧
        b = n / q + Ramsey.ramseyNumber (Erdos1037.r_val n) q + 1}.Nonempty := by
    refine ⟨n / 1 + Ramsey.ramseyNumber (Erdos1037.r_val n) 1 + 1,
      1, by omega, rfl⟩
  have hmem := Nat.sInf_mem hnonempty
  change ramseyDiagonalBound n ∈
    {b : ℕ | ∃ q : ℕ, 0 < q ∧
      b = n / q + Ramsey.ramseyNumber (Erdos1037.r_val n) q + 1} at hmem
  obtain ⟨q, hq, hbound⟩ := hmem
  rw [hbound]
  apply Erdos753.listChromaticNumber_le
  have hchoose := isKChoosable_of_independent_subset G q
    (Ramsey.ramseyNumber (Erdos1037.r_val n) q + 1) hq
    (fun S hS ↦
      exists_independent_subset_of_ramsey_le G S hclique (by omega))
  simpa [Fintype.card_fin, Nat.add_assoc] using hchoose

/-- Exceptional graphs for the chosen sublinear threshold. -/
private def IsExceptional (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ¬ Erdos753.listChromaticNumber G ≤ ramseyDiagonalBound n

/-- Every exceptional graph has a clique at least as large as the logarithmic
threshold. -/
private lemma exceptional_has_largeClique (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : IsExceptional n G) :
    Erdos1037.r_val n ≤ G.cliqueNum := by
  by_contra hnot
  exact hG (listChromaticNumber_le_ramseyDiagonalBound G
    (Nat.lt_of_not_ge hnot))

/-- The exceptional family has asymptotic density zero. -/
theorem exceptionalDensity_tendsto_zero :
    Tendsto (graphDensity IsExceptional) atTop (nhds 0) :=
  graphDensity_tendsto_zero_of_subset_largeClique
    IsExceptional exceptional_has_largeClique

/-- The resolution of Erdős Problem 799: there is a single sublinear bound
which contains the list chromatic number of an asymptotic proportion one of
all labelled graphs. -/
theorem erdos_799 : AlmostAllListChromaticSublinear := by
  refine ⟨ramseyDiagonalBound, ramseyDiagonalBound_isLittleO, ?_⟩
  simpa only [IsExceptional, not_not] using
    graphDensity_not_tendsto_one IsExceptional
      exceptionalDensity_tendsto_zero

end Erdos799

#print axioms Erdos799.erdos_799
