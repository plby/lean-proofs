/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 237.
https://www.erdosproblems.com/forum/thread/237

Formalization status:
- Unconditional; uses only Lean's standard logical axioms.

Informal authors:
- Yong-Gao Chen
- Yuchen Ding

Formal authors:
- Aristotle
- Pietro Monticone

URLs:
- https://www.erdosproblems.com/forum/thread/237#post-5240
- https://gist.githubusercontent.com/pitmonticone/8ea0d1cdb963b6213ac639b11d33f811/raw/98a5824d16da14313f65d77eeab5563dd874613a/Erdos237.lean
-/
/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/
import ErdosProblems.Erdos237b.Unconditional

/-!
# Erdős Problem 237: alternative dyadic sieve proof

This proof establishes a qualitative prime-tuple theorem directly from dyadic
weights, the proved Bombieri–Vinogradov theorem, and ordinary PNT. It does not
use the quantitative Maynard–Tao theorem or the Mertens extraction argument.

The original Chen–Ding reduction using the unconditional quantitative
Maynard–Tao theorem is preserved in `ErdosProblems.Erdos237`.
-/

namespace Erdos237b

open Nat Set Finset Real

/-! ## Chen–Ding theorem -/

/-- **Chen–Ding Theorem** (2022), from the unconditional qualitative prime-tuple theorem. -/
theorem chen_ding_theorem (m : ℕ) :
    ∃ ℓ₀ : ℕ, ∀ (S : Finset ℕ), ℓ₀ ≤ S.card → ∃ n : ℕ, m ≤ repCount (S : Set ℕ) n := by
  exact chen_ding_of_qualitative qualitativePrimeTuples_unconditional m

/-! ## Main result -/

/-- **Erdős Problem 237** (Chen–Ding, 2022). For any infinite set `A ⊆ ℕ`, the representation
function `f_A(n) = #{a ∈ A : (n - a) prime}` is unbounded. -/
theorem erdos_237 (A : Set ℕ) (hA : A.Infinite) :
    ∀ C : ℕ, ∃ n : ℕ, C < repCount A n := by
  intro C
  obtain ⟨ℓ₀, hℓ₀⟩ := chen_ding_theorem (C + 1)
  obtain ⟨S, hS₁, hS₂⟩ := hA.exists_subset_card_eq ℓ₀
  obtain ⟨n, hn⟩ := hℓ₀ S hS₂.ge
  exact ⟨n, (lt_of_succ_le hn).trans_le (repCount_mono hS₁ n)⟩

#print axioms erdos_237
-- 'Erdos237b.erdos_237' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos237b
