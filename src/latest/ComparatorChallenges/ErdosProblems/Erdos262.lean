/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos262

noncomputable def seriesTerm (a t : ℕ → ℕ) (n : ℕ) : ℝ :=
  1 / ((t n : ℝ) * (a n : ℝ))

def IrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ StrictMono a ∧
    ∀ t : ℕ → ℕ, (∀ n, 0 < t n) → Irrational (∑' n, seriesTerm a t n)

noncomputable def doubleLogRatio (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.logb ((2 : ℕ) : ℝ) (Real.logb ((2 : ℕ) : ℝ) (a n : ℝ)) / ((n + 1 : ℕ) : ℝ)

theorem erdos_262 (a : ℕ → ℕ) (h : IrrationalitySequence a) :
    (1 : EReal) ≤ limsup (fun n ↦ (doubleLogRatio a n : EReal)) atTop := by
  sorry

end Erdos262
