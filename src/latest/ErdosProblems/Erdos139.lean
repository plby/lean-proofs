/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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
