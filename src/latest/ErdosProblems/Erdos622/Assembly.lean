/-
Copyright 2026 The Lean-Proofs Authors.

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
import ErdosProblems.Erdos622.Core
import Mathlib.Tactic

/-!
# Assembly of the three structural cases for Erdős Problem 622

The substantive proof divides a regular graph of order `2 * n` into one of
three structural regimes and proves the same uniform lower-density estimate
in each regime.  This file isolates the entirely formal last step: intersect
the four eventual statements, select the applicable case, and convert the
normalized density inequality back into the finite cardinality inequality in
`Resolution`.

The regime predicates are parameters.  Consequently the assembly theorem can
be used with the quantitative definitions employed by the three separate
parts of the proof, without duplicating their parameters here.
-/

open Filter

namespace Erdos622

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A structural regime for graphs on `2 * n` vertices. -/
abbrev GraphRegime :=
  ∀ n : ℕ, SimpleGraph (Fin (2 * n)) → Prop

/-- The density of cyclic subsets under the uniform distribution on all
vertex subsets. -/
def cyclicSubsetDensity {n : ℕ} (G : SimpleGraph (Fin (2 * n))) : ℝ :=
  ((cycleSpannedSubsets G).card : ℝ) / (2 : ℝ) ^ (2 * n)

/-- Multiplying a lower bound for the uniform-subset density by the positive
number of all vertex subsets gives the corresponding finite count bound. -/
theorem cyclicSubsetDensity_lower_iff_count_lower {n : ℕ}
    (G : SimpleGraph (Fin (2 * n))) (c : ℝ) :
    c ≤ cyclicSubsetDensity G ↔
      c * (2 : ℝ) ^ (2 * n) ≤ ((cycleSpannedSubsets G).card : ℝ) := by
  rw [cyclicSubsetDensity, le_div_iff₀]
  positivity

/-- Uniform structural trichotomy on sufficiently large regular graphs. -/
def UniformTrichotomy
    (biDense almostTwoCliques almostBipartite : GraphRegime) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin (2 * n)),
      G.IsRegularOfDegree (n + 1) →
        biDense n G ∨ almostTwoCliques n G ∨ almostBipartite n G

/-- A uniform cyclic-subset density theorem restricted to one structural
regime.  Uniformity in the graph is expressed by placing the graph quantifier
inside the eventual statement. -/
def UniformCaseDensityBound (regime : GraphRegime) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin (2 * n)),
      G.IsRegularOfDegree (n + 1) → regime n G →
        (1 / 2 : ℝ) - ε ≤ cyclicSubsetDensity G

/-- The formal last step of the Draganić--Keevash--Müyesser argument.

Once the structural trichotomy and the lower-density theorem in each of its
three cases have been proved, their uniform eventual forms imply exactly the
epsilon formulation `Resolution`. -/
theorem resolution_of_trichotomy_and_case_density
    {biDense almostTwoCliques almostBipartite : GraphRegime}
    (htrichotomy : UniformTrichotomy biDense almostTwoCliques almostBipartite)
    (hbiDense : UniformCaseDensityBound biDense)
    (halmostTwoCliques : UniformCaseDensityBound almostTwoCliques)
    (halmostBipartite : UniformCaseDensityBound almostBipartite) :
    Resolution := by
  intro ε hε
  filter_upwards [htrichotomy, hbiDense ε hε,
    halmostTwoCliques ε hε, halmostBipartite ε hε] with
      n hcases hbi htwo hbip
  intro G hregular
  apply (cyclicSubsetDensity_lower_iff_count_lower G ((1 / 2 : ℝ) - ε)).mp
  rcases hcases G hregular with hcase | hcase | hcase
  · exact hbi G hregular hcase
  · exact htwo G hregular hcase
  · exact hbip G hregular hcase

end

end Erdos622
