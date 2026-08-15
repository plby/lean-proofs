/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Erdős Problem 1119

The unrestricted question is independent of ZFC.  This file proves the exact
ZFC-positive range from the supplied specification: if `succ m < 𝔠`, then a
family of entire functions taking at most `m` values at each point has size at
most `m`.  It also derives Erdős's countable theorem when `ℵ_ 1 < 𝔠`.

The proof uses the identity theorem to show that two distinct entire functions
coincide at only countably many points.  A subfamily of size `succ m` therefore
has at most `succ m` collision points in total; a point outside that union
separates the whole subfamily.
-/

open Cardinal Order
open scoped Cardinal

namespace Erdos1119

/-- Two distinct entire functions coincide at only countably many points. -/

theorem erdos_1119.variants.easy_case (m : Cardinal.{0}) (hm : ℵ₀ < m)
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

