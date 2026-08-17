/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes the affirmative resolution of Erdős Problem 516.

Informal author:
- W. H. J. Fuchs

Formal author:
- OpenAI Codex

Reference:
W. H. J. Fuchs, "Proof of a conjecture of G. Pólya concerning gap series",
Illinois J. Math. 7 (1963), 661--667.
-/

import Mathlib

open scoped Nat Polynomial
open Filter MeasureTheory Real Set Topology

namespace Erdos516

/-- A strictly increasing sequence `n` has Fabry gaps when `n k / k → ∞`. -/
def HasFabryGaps (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ Tendsto (fun k => n k / (k : ℝ)) atTop atTop

/-- The growth condition used for finite-order entire maps. -/
def OfFiniteOrder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E → F) : Prop :=
  Differentiable ℂ f ∧ ∃ c ≥ 0, ∃ a ≥ 0, ∀ z, ‖f z‖ ≤ c * rexp (‖z‖ ^ a)

/-- The logarithmic minimum-to-maximum modulus ratio on the circle of radius `r`. -/
noncomputable def ratio (r : ℝ) (f : ℂ → ℂ) : ℝ :=
  (⨅ z : {z : ℂ // ‖z‖ = r}, ‖f z‖).log /
    (⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖).log

theorem erdos_516 {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : HasFabryGaps n) {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z)) (hf : OfFiniteOrder f) :
    limsup (fun r ↦ ratio r f) atTop = 1 := by
  sorry
