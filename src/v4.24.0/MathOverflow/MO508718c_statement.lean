import Mathlib

noncomputable def trigamma (z : ℝ) : ℝ := ∑' (n : ℕ), 1 / (n + z)^2

noncomputable def S_sum : ℝ := ∑' k : ℕ, if k = 0 then 0 else (harmonic (2 * k) - harmonic k : ℝ) / ((k : ℝ) ^ 2 * (Nat.choose (2 * k) k : ℝ))

theorem main_theorem : S_sum = 2 * riemannZeta 3 - (Real.pi * Real.sqrt 3 / 24) * trigamma (1/3) + (Real.pi * Real.sqrt 3 / 72) * trigamma (5/6) := by
  sorry
