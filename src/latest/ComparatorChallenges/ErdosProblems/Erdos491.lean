import Mathlib

open Filter Asymptotics

/-- Bounded consecutive differences force a logarithmic main term with bounded residual. -/
theorem erdos_491 (f : ℕ → ℝ)
    (hf : ∀ a b : ℕ, a.Coprime b → f (a * b) = f a + f b)
    (hgap : ∃ C : ℝ, ∀ n : ℕ, |f (n + 1) - f n| < C) :
    ∃ c : ℝ,
      (fun n : ℕ ↦ f n - c * Real.log (n : ℝ)) =O[atTop]
        (fun _ : ℕ ↦ (1 : ℝ)) := by
  sorry
