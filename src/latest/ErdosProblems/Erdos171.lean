/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 171.
https://www.erdosproblems.com/forum/thread/171

Informal authors:
- Pandelis Dodos
- Vassilis Kanellopoulos
- Konstantinos Tyros

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos171.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.DKT

/-!
# Erdős Problem 171

The density Hales--Jewett theorem: every subset of `[t]^N` of fixed positive
density contains a combinatorial line once `N` is sufficiently large.

The proof formalized here follows the uniform-measure density-increment
argument of Dodos--Kanellopoulos--Tyros.  Its principal inputs are the
Hales--Jewett theorem, a derived line-coloring Graham--Rothschild theorem,
Sperner's theorem for the binary base case, uniform-fibre regularization,
structured correlation by insensitive sets, and a greedy subspace tiling.
-/

namespace Erdos171

/-- The affirmative resolution of Erdős Problem 171. -/
theorem erdos_171 : Erdos171Statement :=
  erdos171Statement_of_alphabetDensityIncrement alphabetDensityIncrement

#print axioms Erdos171.erdos_171

end Erdos171
