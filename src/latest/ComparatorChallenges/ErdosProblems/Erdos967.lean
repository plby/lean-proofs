/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

set_option linter.style.longLine false
set_option aesop.warn.nonterminal false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos967

open Classical in
def question_1_1_statement : Prop :=
  ∀ (S : Set ℕ), (∀ n ∈ S, 1 < n) →
  Summable (fun n => if n ∈ S then (n : ℝ)⁻¹ else 0) →
  ∀ (t : ℝ), 1 + (∑' n, if n ∈ S then (n : ℂ) ^ (-(1 + Complex.I * t)) else 0) ≠ 0
end Erdos967

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos967

open scoped Classical in
theorem main_theorem (t : ℝ) (ht : t ≠ 0) (lambda_val : ℂ) :
  ∃ S : Set ℕ, (∀ n ∈ S, n ≥ 2) ∧
  Summable (fun n => if n ∈ S then (n : ℝ)⁻¹ else 0) ∧
  (∑' n, if n ∈ S then (n : ℂ) ^ (-(1 + Complex.I * t)) else 0) = lambda_val := by
  sorry

end Erdos967
open scoped Classical in
theorem Erdos967.disproof_of_question_1_1 :
    Not Erdos967.question_1_1_statement
  := by
  sorry
