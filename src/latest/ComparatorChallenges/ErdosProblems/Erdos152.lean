/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 152

#TODO: Formalize the corresponding conjecture for infinite Sidon sets.

*References:*
 - [erdosproblems.com/152](https://www.erdosproblems.com/152)
 - [ESS94] Erdős, P. and Sárközy, A. and Sós, T., On Sum Sets of Sidon Sets, I. Journal of Number
    Theory (1994), 329-347.
-/

open scoped Pointwise Asymptotics
open Filter

namespace Erdos152

/-- Local compatibility syntax for the upstream Formal Conjectures statement. -/
syntax:max "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

/-- `g ≫ h` means that `h` is big-O of `g` at infinity. -/
notation:50 g " ≫ " h => Asymptotics.IsBigO Filter.atTop h g

/-- A Sidon set has unique unordered two-term sums. -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)


/-- Define `f n` to be the minimum of `|{s | s - 1 ∉ A + A, s ∈ A + A, s + 1 ∉ A + A}|` as `A`
ranges over all Sidon sets of size `n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  ⨅ A : {A : Set ℕ | A.ncard = n ∧ IsSidon A},
  {s : ℕ | s - 1 ∉ A.1 + A.1 ∧ s ∈ A.1 + A.1 ∧ s + 1 ∉ A.1 + A.1}.ncard



open scoped Classical



open Set Finset

noncomputable def num_isolated (A : Set ℕ) : ℕ :=
  {s : ℕ | s - 1 ∉ A + A ∧ s ∈ A + A ∧ s + 1 ∉ A + A}.ncard

noncomputable def N_k_N (X : Set ℕ) (k : ℕ) : ℕ := {x ∈ X | x + k ∈ X}.ncard
noncomputable def N_k_Z (X : Set ℤ) (k : ℤ) : ℕ := {x ∈ X | x + k ∈ X}.ncard
noncomputable def V_2_N (X : Set ℕ) : ℕ := {x ∈ X | x - 1 ∈ X ∧ x + 1 ∈ X}.ncard
noncomputable def I_N (X : Set ℕ) : ℕ := {x ∈ X | x - 1 ∉ X ∧ x + 1 ∉ X}.ncard

noncomputable def D_set (A : Set ℕ) : Set ℤ :=
  {z : ℤ | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ z = (a : ℤ) - (b : ℤ)}

noncomputable def ind (X : Set ℤ) (x : ℤ) : ℤ := if x ∈ X then 1 else 0

theorem erdos_152.variants.square : answer(True) ↔
    (fun n => f n : ℕ → ℝ) ≫ (fun n => n ^ 2 : ℕ → ℝ) := by
  sorry

