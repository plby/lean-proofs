import Mathlib

open Real Filter Asymptotics

noncomputable abbrev nth_prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

axiom nth_prime_asymp :
    (fun n ↦ ((nth_prime n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) * Real.log (n : ℝ))
