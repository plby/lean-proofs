/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.AffinePrimePairs

/-!
# Parameterizing primitive linear collisions

After dividing the common coefficient gcd, two prime variables in a
collision satisfy a primitive linear equation.  Relative to any least
solution, every other solution advances by the opposite coefficient in each
coordinate.  This is the elementary bridge from collision pairs to the
two-affine prime-candidate sieve.
-/

namespace Erdos822

/-- Two ordered solutions of a primitive linear equation differ by one common
natural parameter: the first coordinate advances by B and the second by A. -/
theorem exists_common_parameter_of_coprime_linear_eq
    {A B p q p' q' : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hcop : A.Coprime B)
    (hqp : q ≤ p) (hq'p' : q' ≤ p')
    (heq : A * p + B * q' = A * q + B * p') :
    ∃ k : ℕ, p = q + B * k ∧ p' = q' + A * k := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hqp
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hq'p'
  have huv : A * u = B * v := by
    nlinarith
  have hBdvd : B ∣ A * u := ⟨v, huv⟩
  have hBu : B ∣ u := hcop.symm.dvd_of_dvd_mul_left hBdvd
  obtain ⟨k, rfl⟩ := hBu
  have hv : v = A * k := by
    nlinarith
  exact ⟨k, by ring, by simpa [hv]⟩

/-- The common parameter is unique as soon as the opposite coefficient is
positive. -/
theorem common_parameter_unique
    {B p q k l : ℕ} (hB : 0 < B)
    (hk : p = q + B * k) (hl : p = q + B * l) : k = l := by
  have hmul : B * k = B * l := by omega
  exact Nat.mul_left_cancel hB hmul

end Erdos822
