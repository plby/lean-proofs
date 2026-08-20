/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.PadicSubspaceDefs
import ErdosProblems.Erdos407.ExteriorFinal

/-!
# The rational `{infinity, 2, 3}` Subspace-Theorem interface

This public module re-exports the elementary rational three-place definitions
and the exterior-power endpoint.  Keeping the elementary layer in
`PadicSubspaceDefs` lets the analytic modules depend on it without forming a
cycle through the endpoint.
-/
