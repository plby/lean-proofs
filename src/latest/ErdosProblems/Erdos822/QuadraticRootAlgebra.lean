/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.QuadraticResidueRelation
import Mathlib.Data.ZMod.Basic

/-!
# Quadratic roots over domains

The safe local statement is first proved over an integral domain: two roots
of `T^2 - v*T + u` are either equal or have sum `v`.  In particular three
roots cannot be pairwise distinct.  This avoids silently assuming a false
prime-power root bound in the repeated-root case.
-/

namespace Erdos822

/-- Two roots of a monic quadratic over an integral domain are equal or
their sum is the linear coefficient. -/
theorem quadratic_roots_eq_or_add_eq
    {R : Type*} [CommRing R] [IsDomain R]
    {a b u v : R}
    (ha : a ^ 2 + u = v * a)
    (hb : b ^ 2 + u = v * b) :
    a = b ∨ a + b = v := by
  have hfactor : (a - b) * (a + b - v) = 0 := by
    calc
      (a - b) * (a + b - v) =
          (a ^ 2 + u - v * a) - (b ^ 2 + u - v * b) := by ring
      _ = 0 := by rw [ha, hb]; ring
  rcases mul_eq_zero.mp hfactor with hab | hsum
  · left
    exact sub_eq_zero.mp hab
  · right
    exact sub_eq_zero.mp hsum

/-- Among three roots of one monic quadratic over a domain, two coincide. -/
theorem three_quadratic_roots_two_eq
    {R : Type*} [CommRing R] [IsDomain R]
    {a b c u v : R}
    (ha : a ^ 2 + u = v * a)
    (hb : b ^ 2 + u = v * b)
    (hc : c ^ 2 + u = v * c) :
    a = b ∨ a = c ∨ b = c := by
  rcases quadratic_roots_eq_or_add_eq ha hb with hab | habsum
  · exact Or.inl hab
  rcases quadratic_roots_eq_or_add_eq ha hc with hac | hacsum
  · exact Or.inr (Or.inl hac)
  right
  right
  exact add_left_cancel (habsum.trans hacsum.symm)

/-- Specialization to a prime residue field.  This is the exact local
two-root fact used before assembling squarefree moduli by CRT. -/
theorem three_quadratic_roots_mod_prime_two_eq
    {p : ℕ} (hp : p.Prime)
    {a b c u v : ZMod p}
    (ha : a ^ 2 + u = v * a)
    (hb : b ^ 2 + u = v * b)
    (hc : c ^ 2 + u = v * c) :
    a = b ∨ a = c ∨ b = c := by
  letI : Fact p.Prime := ⟨hp⟩
  exact three_quadratic_roots_two_eq ha hb hc

end Erdos822
