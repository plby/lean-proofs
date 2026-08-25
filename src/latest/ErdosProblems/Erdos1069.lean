/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1069.
https://www.erdosproblems.com/forum/thread/1069

Informal authors:
- Endre Szemerédi
- William T. Trotter Jr.

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1069.md
-/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import Util.IncidenceGeometry.RichLinesBound

/-!
# Erdős Problem 1069

There is an absolute constant `C` such that, for every finite set `P` of
points in the real affine plane and every `k` with `2 ≤ k ≤ sqrt |P|`, the
number of affine lines containing at least `k` points of `P` is at most
`C |P|² / k³`.

The condition `2 ≤ k` is necessary: through a single point there are
infinitely many affine lines.  It also makes the family of all `k`-rich lines
finite, since each such line is determined by a pair of distinct points.

The Szemerédi--Trotter theorem and the complete reduction from its incidence
bound to the rich-line estimate are provided by the checked theorem
`RichLinesBound`.
-/

open Classical
open scoped Real

noncomputable section

namespace Erdos1069

/-- The real Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Affine lines in the real Euclidean plane. -/
abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

/-- The number of points of `P` lying on `ℓ`. -/
noncomputable def richness (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter fun p ↦ p ∈ (ℓ : AffineSubspace ℝ Point)).card

/-- **Erdős Problem 1069 (Szemerédi--Trotter).**

There is one absolute positive constant bounding, for every finite planar
point set and every `2 ≤ k ≤ sqrt |P|`, the cardinality of the family of all
`k`-rich affine lines by `C |P|² / k³`.  The biconditional says that `L`
enumerates all such lines, so its cardinality is exactly the number in the
problem statement. -/
theorem erdos_1069 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset Point) (k : ℕ),
        2 ≤ k → (k : ℝ) ≤ Real.sqrt (P.card : ℝ) →
          ∃ L : Finset Line,
            (∀ ℓ, ℓ ∈ L ↔ k ≤ richness P ℓ) ∧
            (L.card : ℝ) ≤ C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := by
  simpa only [richness] using RichLinesBound

#print axioms erdos_1069

end Erdos1069
