/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 651.
https://www.erdosproblems.com/forum/thread/651

Informal authors:
- Cosmin Pohoata
- Dmitrii Zakharov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos651.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Asymptotic

/-!
# Erdős Problem 651

For `d ≥ 2`, the higher-dimensional Erdős--Szekeres number is the least
cardinality which forces a prescribed number of points in convex position
inside every general-position point set in `ℝ^d`.

Pohoata and Zakharov proved that the three-dimensional numbers are
subexponential.  The main result below formalizes the exact logical content
of their resolution: a `2^{o(n)}` upper bound is incompatible with Erdős's
proposed fixed-base exponential lower bound.

The accompanying mathematical reconstruction, including all geometric
ingredients of Pohoata--Zakharov's proof, is in `tex/651.tex`.
-/

namespace Erdos651

noncomputable section

/-- The Pohoata--Zakharov conclusion gives the negative answer to Problem
651 in dimension three. -/
theorem erdos_651_of_pohoata_zakharov
    (hPZ : PohoataZakharovConclusion) :
    ¬ Erdos651Claim :=
  subexponential_not_exponentialLowerBound hPZ

/-- Unconditional incompatibility formulation of the established resolution:
the published subexponential conclusion and Erdős's proposed exponential
lower bound cannot both hold for `f₃`. -/
theorem not_erdos_651 :
    ¬ ((Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber 3)) ∧ (Erdos651.HasExponentialLowerBound (Erdos651.erdosSzekeresNumber 3))) := by
  rintro ⟨hPZ, hErdos⟩
  exact erdos_651_of_pohoata_zakharov hPZ hErdos

end

end Erdos651

#print axioms Erdos651.not_erdos_651

alias _root_.Erdos651.erdos_651 := _root_.Erdos651.not_erdos_651
