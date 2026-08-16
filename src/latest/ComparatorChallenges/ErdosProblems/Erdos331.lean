import Mathlib

namespace Erdos331

set_option linter.style.longLine false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Nat Filter
open scoped Asymptotics

set_option relaxedAutoImplicit false
set_option autoImplicit false

@[instance_reducible] noncomputable def instDecidablePredNat_erdosProblems (A : Set Nat) : DecidablePred A :=
  Classical.decPred A

end Erdos331

open Erdos331

attribute [local instance] Classical.propDecidable


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Nat Filter
open scoped Asymptotics

namespace Erdos331

attribute [local instance] instDecidablePredNat_erdosProblems

theorem main_theorem : ∃ (A' B' : Set ℕ),
  (∀ x ∈ A', x > 0) ∧ (∀ x ∈ B', x > 0) ∧
  (∃ N₀, ∀ N ≥ N₀,
    ((Finset.Icc 1 N).filter (· ∈ A')).card ≥ (1/4 : ℝ) * Real.sqrt N ∧
    ((Finset.Icc 1 N).filter (· ∈ B')).card ≥ (1/4 : ℝ) * Real.sqrt N) ∧
  (∀ a₁ ∈ A', ∀ a₂ ∈ A', ∀ b₁ ∈ B', ∀ b₂ ∈ B',
    a₁ ≠ a₂ → a₁ - (a₂ : ℤ) ≠ b₁ - (b₂ : ℤ)) := by
  sorry


theorem erdos_331 :
    ¬(∀ A B : Set ℕ,
      (fun (n : ℕ) ↦ (n : ℝ) ^ (1 / 2 : ℝ)) =O[atTop]
        (fun (n : ℕ) ↦ (count A n : ℝ)) →
      (fun (n : ℕ) ↦ (n : ℝ) ^ (1 / 2 : ℝ)) =O[atTop]
        (fun (n : ℕ) ↦ (count B n : ℝ)) →
      { s : ℕ × ℕ × ℕ × ℕ |
        let a₁ := s.1
        let a₂ := s.2.1
        let b₁ := s.2.2.1
        let b₂ := s.2.2.2
        a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
        a₁ ≠ a₂ ∧ a₁ + b₂ = a₂ + b₁ }.Infinite) := by
  sorry

end Erdos331
