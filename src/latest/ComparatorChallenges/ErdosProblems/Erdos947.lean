/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos947

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

def IsExactCoveringSystem (l : List (ℤ × ℕ)) : Prop :=
  (∀ p ∈ l, 0 ≤ p.1 ∧ p.1 < p.2) ∧
  (∀ m : ℤ, ∃! i : Fin l.length, let (a, n) := l.get i; m ≡ a [ZMOD n])
open PowerSeries

open PowerSeries

open PowerSeries

open PowerSeries

open Polynomial

open Polynomial

end Erdos947


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open PowerSeries
open Polynomial

namespace Erdos947

open scoped Classical in
theorem exact_covering_system_distinct_moduli_impossible
    (l : List (ℤ × ℕ)) (h_exact : IsExactCoveringSystem l)
    (h_distinct : l.Pairwise (fun p q => p.2 ≠ q.2)) (h_len : l.length ≥ 2) : False := by
  sorry

end Erdos947
