/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# A bounded finite-deletion engine

This file isolates the well-founded induction that turns a one-step deletion
lemma into a terminal core.  The objects being simplified are finite sets, but
the termination argument uses only a natural-valued potential.

We express the assertion that at most `budget` elements are deleted in one
step as

`A.card ≤ B.card + budget`.

This formulation avoids truncated subtraction.  After at most `μ A` strict
decreases of the potential, the accumulated loss is at most
`budget * μ A`.
-/

namespace Erdos186.CFP

section

variable {α : Type*}

/-- A bounded deletion process whose natural-valued potential strictly drops
at every nonterminal state reaches a good subset.  Its total cardinality loss
is at most the one-step budget times the initial potential.

The theorem does not require `Good` to be hereditary, nor does it require the
potential to be monotone under arbitrary inclusions.  Only the explicitly
supplied deletion step is used. -/
theorem exists_good_subset_of_decreasing_potential
    (Good : Finset α → Prop) (μ : Finset α → ℕ) (budget : ℕ)
    (step : ∀ A : Finset α, ¬ Good A →
      ∃ B : Finset α, B ⊆ A ∧
        A.card ≤ B.card + budget ∧ μ B < μ A) :
    ∀ A : Finset α, ∃ B : Finset α, B ⊆ A ∧ Good B ∧
      A.card ≤ B.card + budget * μ A := by
  intro A
  generalize hn : μ A = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
      by_cases hgood : Good A
      · exact ⟨A, fun _ ha ↦ ha, hgood, Nat.le_add_right _ _⟩
      · obtain ⟨B, hBA, hloss, hμ⟩ := step A hgood
        have hμn : μ B < n := by simpa [← hn] using hμ
        obtain ⟨C, hCB, hCgood, hBC⟩ := ih (μ B) hμn B rfl
        refine ⟨C, hCB.trans hBA, hCgood, ?_⟩
        have hpotential : budget * (μ B + 1) ≤ budget * n :=
          Nat.mul_le_mul_left budget (Nat.succ_le_iff.mpr hμn)
        calc
          A.card ≤ B.card + budget := hloss
          _ ≤ (C.card + budget * μ B) + budget :=
            Nat.add_le_add_right hBC budget
          _ = C.card + budget * (μ B + 1) := by
            simp [Nat.mul_succ, Nat.add_assoc]
          _ ≤ C.card + budget * n := Nat.add_le_add_left hpotential C.card

/-- Invariant-preserving version of
`exists_good_subset_of_decreasing_potential`.

Only sets satisfying `Inv` need a deletion step, and every chosen
successor is required to satisfy `Inv` again.  This is useful when the process
must retain an anchor or another structural feature: there is no need to
invent a deletion step for finite sets outside the invariant. -/
theorem exists_good_invariant_subset_of_decreasing_potential
    (Inv Good : Finset α → Prop) (μ : Finset α → ℕ) (budget : ℕ)
    (step : ∀ A : Finset α, Inv A → ¬ Good A →
      ∃ B : Finset α, B ⊆ A ∧ Inv B ∧
        A.card ≤ B.card + budget ∧ μ B < μ A) :
    ∀ A : Finset α, Inv A →
      ∃ B : Finset α, B ⊆ A ∧ Inv B ∧ Good B ∧
        A.card ≤ B.card + budget * μ A := by
  intro A hAInv
  generalize hn : μ A = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
      by_cases hgood : Good A
      · exact ⟨A, fun _ ha ↦ ha, hAInv, hgood, Nat.le_add_right _ _⟩
      · obtain ⟨B, hBA, hBInv, hloss, hμ⟩ := step A hAInv hgood
        have hμn : μ B < n := by simpa [← hn] using hμ
        obtain ⟨C, hCB, hCInv, hCgood, hBC⟩ :=
          ih (μ B) hμn B hBInv rfl
        refine ⟨C, hCB.trans hBA, hCInv, hCgood, ?_⟩
        have hpotential : budget * (μ B + 1) ≤ budget * n :=
          Nat.mul_le_mul_left budget (Nat.succ_le_iff.mpr hμn)
        calc
          A.card ≤ B.card + budget := hloss
          _ ≤ (C.card + budget * μ B) + budget :=
            Nat.add_le_add_right hBC budget
          _ = C.card + budget * (μ B + 1) := by
            simp [Nat.mul_succ, Nat.add_assoc]
          _ ≤ C.card + budget * n := Nat.add_le_add_left hpotential C.card

end

end Erdos186.CFP
