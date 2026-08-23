/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 722.
https://www.erdosproblems.com/forum/thread/722

Informal authors:
- Peter Keevash

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos722.md
-/
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
import ErdosProblems.Erdos722.FinalAssembly

/-!
# Erdős Problem 722

For fixed `k > r ≥ 1`, every sufficiently large admissible order supports
a Steiner system `S(r, k, n)`.  This is the existence theorem proved by
Keevash, with the exact divisibility conditions encoded by
`Erdos722.IsAdmissible`.
-/

namespace Erdos722

/-- Resolution of Erdős Problem 722: the standard divisibility conditions
are sufficient for all sufficiently large orders. -/
theorem erdos_722 : Resolution := by
  apply resolution_of_eventual_sparseIntegralGeneratorData
  intro k r hr hrk
  exact eventually_hasSparseIntegralGeneratorData k r hr hrk

#print axioms erdos_722

end Erdos722
