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
import ErdosProblems.Erdos608.Assembly
import ErdosProblems.Erdos608.Cycle5
import ErdosProblems.Erdos608.Sanity

namespace Erdos608

theorem not_erdos_608 :
    ¬ (∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
      n ^ 2 < 4 * G.edgeSet.ncard → 2 * n ^ 2 ≤ 9 * (pentEdges G).ncard) := disproof

#print axioms not_erdos_608
-- 'Erdos608.not_erdos_608' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms strong_disproof
-- 'Erdos608.strong_disproof' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms onC5_iff_cycle
-- 'Erdos608.onC5_iff_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos608
