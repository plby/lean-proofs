/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1081.
https://www.erdosproblems.com/forum/thread/1081

Informal authors:
- Valentin Blomer
- Andrew Granville

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1081.md
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

import ErdosProblems.Erdos1081.Erdos1081KernelLower
import ErdosProblems.Erdos1081.Erdos1081OddClass

/-!
# Erdős Problem 1081

This module gives the unconditional negative answer to Erdős Problem 1081.
The exact squarefull-sum counting function and all intermediate estimates are
defined in the imported companion modules.
-/

namespace Erdos1081

noncomputable section

/-- The uniform fixed-form lower bound needed by the diagonal argument.  Its
remaining square-subgroup hypothesis is discharged by the oddness theorem for
the class group of the order of discriminant `-4p³`. -/
theorem specialBernaysLower : SpecialBernaysLower := by
  apply specialBernaysLower_of_squareSubgroup_top
  intro p _inst hp4
  exact special_classSquareSubgroup_eq_top hp4

/-- Erdős's proposed asymptotic for sums of two positive squarefull numbers is
false. -/
theorem not_erdosConjecture : ¬ ErdosConjecture :=
  not_erdosConjecture_of_specialBernaysLower specialBernaysLower

#print axioms not_erdosConjecture

end


end Erdos1081
