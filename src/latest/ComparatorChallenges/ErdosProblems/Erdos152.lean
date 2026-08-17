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

theorem erdos_152.variants.square :
    (fun n => f n : ℕ → ℝ) ≫ (fun n => n ^ 2 : ℕ → ℝ) := by
  sorry

