/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos291b

def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

def z (m : ℕ) : ℕ := ((Finset.range m).filter Nat.Prime).card

def X_int (r : ℕ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, r i * ((L n) / i : ℕ)

theorem erdos_291 (r : ℕ → ℤ) (t : ℕ) (ht : t > 0) (h_per : Function.Periodic r t)
    (h_r_nz : ∀ i, r i ≠ 0)
    (h_priemteller : ∀ m : ℕ, m ≥ 4 → (m : ℝ)^(2 * z m) < Real.exp (2.52 * m))
    (h_bla0 : ∀ n : ℕ, n ≥ 100 → L n > 2^n) :
    ∀ N, ∃ b, Nat.gcd (Int.natAbs (X_int r b)) (L b) > N := by
  sorry

end Erdos291b
