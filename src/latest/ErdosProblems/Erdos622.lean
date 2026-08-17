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
import ErdosProblems.Erdos622.Regimes
import ErdosProblems.Erdos622.BiDenseCase
import ErdosProblems.Erdos622.AlmostCliques
import ErdosProblems.Erdos622.AlmostBipartiteCase

/-!
# Erdős Problem 622

Every sufficiently large `(n + 1)`-regular graph on `2 * n` vertices has
asymptotically at least half of all vertex subsets spanned by a cycle.

The proof combines the checked structural trichotomy with the independently
proved uniform density bound in each of its bi-dense, almost-two-cliques, and
almost-bipartite branches.
-/

namespace Erdos622

/-- Resolution of Erdős Problem 622: uniformly over `(n + 1)`-regular graphs
on `2 * n` vertices, the density of vertex subsets spanned by a cycle has
limit inferior at least `1 / 2`. -/
theorem erdos_622 : Resolution :=
  resolution_of_trichotomy_and_case_density
    uniform_regime_trichotomy
    BiDenseCase.uniformCaseDensityBound_biDense
    AlmostCliques.uniformCaseDensityBound_almostTwoCliques_root
    AlmostBipartiteCase.uniformCaseDensityBound_almostBipartite

#print axioms erdos_622

end Erdos622
