/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 139.
https://www.erdosproblems.com/forum/thread/139

Informal authors:
- Endre Szemerédi

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos139.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/139.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Wikipedia.SzemeredisTheorem

open scoped Topology

namespace Erdos139

noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

/-- Erdős Problem 139: the largest `k`-AP-free subset of `{1, ..., N}`
has cardinality `o(N)`. -/
theorem erdos_139 (k : ℕ) (hk : 1 < k) :
    Filter.Tendsto (fun N => (r k N / N : ℝ)) Filter.atTop (𝓝 0) :=
  SzemeredisTheorem.szemeredis_theorem k hk

end Erdos139
