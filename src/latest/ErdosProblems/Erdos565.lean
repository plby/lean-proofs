/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 565.
https://www.erdosproblems.com/forum/thread/565

Informal authors:
- Luís Aragão
- Marcelo Campos
- Gabriel Dahia
- Rafael Filipe
- João Pedro Marciano

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos565.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
import ErdosProblems.Erdos565.FinalAssembly

/-!
# Erdős problem 565

This file records the affirmative resolution of the Erdős--Rödl problem on
induced Ramsey numbers.  In the labelled finite-graph formulation, every
graph on `n` vertices has an induced Ramsey host with at most `2^(3000*n)`
vertices.  Consequently its least induced Ramsey order satisfies the same
bound.
-/

namespace Erdos565

/-- **Resolution of Erdős problem 565.**  Every graph on `n` vertices admits
an induced Ramsey host with at most `2^(3000*n)` vertices. -/
theorem erdos_565 (n : ℕ) (G : SimpleGraph (Fin n)) :
    HasInducedRamseyOrderAtMost G (2 ^ (3000 * n)) :=
  FinalAssembly.hasInducedRamseyOrderAtMost_explicit n G

/-- The uniform formulation of the explicit exponential bound. -/
theorem erdos_565_uniform :
    UniformInducedRamseyBound (fun n ↦ 2 ^ (3000 * n)) :=
  FinalAssembly.uniformInducedRamseyBound_explicit

/-- The corresponding upper bound for the least induced Ramsey order. -/
theorem erdos_565_inducedRamseyNumber_le (n : ℕ)
    (G : SimpleGraph (Fin n)) :
    inducedRamseyNumber G ((erdos_565 n G).exists) ≤ 2 ^ (3000 * n) :=
  inducedRamseyNumber_le_of_hasAtMost G ((erdos_565 n G).exists)
    (erdos_565 n G)

end Erdos565

#print axioms Erdos565.erdos_565
#print axioms Erdos565.erdos_565_uniform
#print axioms Erdos565.erdos_565_inducedRamseyNumber_le
