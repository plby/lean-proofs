/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 1119

The unrestricted question is independent of ZFC.  The positive range asserts
that if `succ m < 𝔠`, a family of entire functions taking at most `m` values at
each point has size at most `m`.  The second statement is Erdős's countable
theorem when `ℵ_ 1 < 𝔠`.
-/

open Cardinal Order
open scoped Cardinal

namespace Erdos1119

theorem erdos_1119.variants.easy_case (m : Cardinal) (hm : ℵ₀ < m)
    (hsucc : succ m < 𝔠) (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f)
    (hval : ∀ z : ℂ, #{y : ℂ | ∃ f ∈ F, f z = y} ≤ m) :
    #F ≤ m := by
  sorry

theorem erdos_1119.variants.erdos_wetzel
    (h : (ℵ_ 1 : Cardinal.{0}) < 𝔠) (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f)
    (hval : ∀ z : ℂ, {y : ℂ | ∃ f ∈ F, f z = y}.Countable) :
    F.Countable := by
  sorry
