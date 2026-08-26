import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Algebraic extraction from the interval-overlap count

Plagne's equations (3.10)--(3.11) produce the doubled overlap inequality used
below.  This file verifies, independently of the geometric derivation, that
this inequality has precisely the Deléglise coefficient and hence leading
constant `1/3`.
-/

namespace Erdos336.Problem336

/-- The overlap coefficient. -/
def overlapCoeff (r s q : ℕ) : ℕ := (r + 1) * (s + q) + s * q

/-- Algebraic form of the passage from Plagne's overlap inequality to the
circle-size bound. -/
theorem interval_bound_of_overlap
    (h r s q V m : ℕ)
    (hsum : h = r + s + q)
    (hoverlap :
      2 * m + V * (s * (s - 1) + q * (q - 1) + r * (r + 1)) + 2 * r ≤
        V * (h * (h + 1)) + 2 * h) :
    m ≤ V * overlapCoeff r s q + h := by
  subst h
  have hid :
      (r + s + q) * (r + s + q + 1) =
        2 * overlapCoeff r s q +
          (s * (s - 1) + q * (q - 1) + r * (r + 1)) := by
    rcases s with _ | s <;> rcases q with _ | q <;>
      simp [overlapCoeff] <;> ring
  rw [hid] at hoverlap
  simp only [Nat.mul_add] at hoverlap
  have hdouble :
      V * (2 * overlapCoeff r s q) = 2 * (V * overlapCoeff r s q) := by
    ring
  rw [hdouble] at hoverlap
  omega

/-- Assumption-free quadratic optimization of the same coefficient. -/
theorem overlapCoeff_coarse
    (h r s q : ℕ) (hsum : h = r + s + q) :
    3 * overlapCoeff r s q ≤ (h + 1) ^ 2 := by
  let A : ℤ := 3 * ((s + q : ℕ) : ℤ) - 2 * ((h + 1 : ℕ) : ℤ)
  let B : ℤ := (s : ℤ) - (q : ℤ)
  have ident :
      (4 : ℤ) * (((h + 1 : ℕ) : ℤ) ^ 2) -
          12 * (overlapCoeff r s q : ℤ) = A ^ 2 + 3 * B ^ 2 := by
    dsimp [A, B, overlapCoeff]
    push_cast
    nlinarith
  have hsqa : 0 ≤ A ^ 2 := sq_nonneg A
  have hsqb : 0 ≤ B ^ 2 := sq_nonneg B
  have cast_bound :
      (3 : ℤ) * (overlapCoeff r s q : ℤ) ≤
        (((h + 1 : ℕ) : ℤ) ^ 2) := by
    nlinarith
  exact_mod_cast cast_bound

/-- Combined consequence: the geometric overlap inequality forces the uniform
bound `3m ≤ V(h+1)^2+3h`. -/
theorem interval_coarse_bound_of_overlap
    (h r s q V m : ℕ)
    (hsum : h = r + s + q)
    (hoverlap :
      2 * m + V * (s * (s - 1) + q * (q - 1) + r * (r + 1)) + 2 * r ≤
        V * (h * (h + 1)) + 2 * h) :
    3 * m ≤ V * (h + 1) ^ 2 + 3 * h := by
  have hm := interval_bound_of_overlap h r s q V m hsum hoverlap
  have hD := overlapCoeff_coarse h r s q hsum
  nlinarith

end Erdos336.Problem336
