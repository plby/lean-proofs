/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 163.
https://www.erdosproblems.com/forum/thread/163

Informal authors:
- Choongbum Lee

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos163.md
-/
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
import ErdosProblems.Erdos163.LargeOrder

/-!
# Erdős Problem 163: the Burr--Erdős conjecture

Choongbum Lee proved that, for each fixed `d`, the Ramsey number of every
`d`-degenerate graph is linear in its number of vertices.  Here degeneracy is
stated in the equivalent induced-subgraph form: every nonempty vertex set
contains a vertex of induced degree at most `d`.

The quantitative large-order argument is formalized in
`ErdosProblems.Erdos163.LargeOrder`; the finitely many smaller target orders
are absorbed into the constant in `ErdosProblems.Erdos163.Conclusion`.
-/

namespace Erdos163

/-- Erdős Problem 163 (the Burr--Erdős conjecture), resolved by Lee: for every
`d ≥ 1` there is a constant depending only on `d` such that every
`d`-degenerate graph on `n` vertices has Ramsey number at most `C * n`. -/
theorem erdos_163 :
    ∀ d : ℕ, 1 ≤ d →
      ∃ C : ℕ, 1 ≤ C ∧
        ∀ n : ℕ, ∀ H : SimpleGraph (Fin n),
          IsDegenerateAtMost H d → RamseyFor H (C * n) :=
  erdos_163_of_large_order largeOrderDegenerateRamsey

end Erdos163
