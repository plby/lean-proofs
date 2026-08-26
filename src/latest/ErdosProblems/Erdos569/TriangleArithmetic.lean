/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.TriangleTwoArithmetic
import Mathlib.Tactic.IntervalCases

/-! # Removing the bounded-order cutoff from the triangle arithmetic -/

namespace Erdos569

open Erdos570

/-- The degree-two extension inequalities also hold below the order cutoff
in the existing eventual-bound proof. The linear constraints leave only
seven triples of clique size, deficit, and outside order. -/
theorem triangle_degree_two_extension_arithmetic
    {m p s t f y : ℕ} (hf : 1 ≤ f)
    (hpf : p = t + f) (hhostLower : 2 * m + 1 ≤ t + y)
    (hhostUpper : t + y + 1 ≤ p + 2 * t)
    (hdegrees : 3 * p ≤ 2 * m + s)
    (hindependent : 2 * s ≤ m) (hsp : s ≤ p) :
    2 * f < t ∧ t ≤ y ∧ t * (y - t) ≥ y ∧
      y * (t - 1) * f ≤
        (y - t) * (t * (y - t) - y) ∧
      let σ := y - 2 * t
      σ < f → 2 ≤ f →
        y * (t - 1) * (σ * s + (f - σ) * (y - t - σ)) ≤
          s * (y - t) * (t * (y - t) - y) := by
  by_cases hp11 : 11 ≤ p
  · exact Erdos570.triangle_degree_two_extension_arithmetic
      hf hp11 hpf hhostLower hhostUpper hdegrees hindependent hsp
  have hcases :
      (t = 7 ∧ f = 1 ∧ y = 14) ∨
      (t = 8 ∧ f = 1 ∧ (y = 15 ∨ y = 16)) ∨
      (t = 8 ∧ f = 2 ∧ y = 17 ∧ s = 6) ∨
      (t = 9 ∧ f = 1 ∧ (y = 16 ∨ y = 17 ∨ y = 18)) := by
    have hp10 : p ≤ 10 := by omega
    interval_cases p <;> omega
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hy⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, hy⟩
  · norm_num
  · rcases hy with rfl | rfl <;> norm_num
  · norm_num
  · rcases hy with rfl | rfl | rfl <;> norm_num

end Erdos569
