import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Assumption-free coarse Deléglise optimization

The sharp residue corrections require positivity and coprimality of the two
distance parameters.  For the asymptotic constant in Erdős Problem 336, the
following stronger-in-generality estimate is sufficient.
-/

namespace Erdos336.Problem336

/-- The overlap coefficient in the interval-cover calculation. -/
def intervalOverlapD (r s q : ℕ) : ℕ := (r + 1) * (s + q) + s * q

/-- For arbitrary nonnegative `r,s,q` summing to `h`, the interval-cover
overlap coefficient is at most `(h+1)^2/3`. -/
theorem intervalOverlapD_coarse_bound
    (h r s q : ℕ) (h_eq : h = r + s + q) :
    3 * intervalOverlapD r s q ≤ (h + 1) ^ 2 := by
  let A : ℤ := 3 * ((s + q : ℕ) : ℤ) - 2 * ((h + 1 : ℕ) : ℤ)
  let B : ℤ := (s : ℤ) - (q : ℤ)
  have ident :
      (4 : ℤ) * (((h + 1 : ℕ) : ℤ) ^ 2) -
          12 * (intervalOverlapD r s q : ℤ) = A ^ 2 + 3 * B ^ 2 := by
    dsimp [A, B, intervalOverlapD]
    push_cast
    nlinarith
  have hsqa : 0 ≤ A ^ 2 := sq_nonneg A
  have hsqb : 0 ≤ B ^ 2 := sq_nonneg B
  have cast_bound :
      (3 : ℤ) * (intervalOverlapD r s q : ℤ) ≤
        (((h + 1 : ℕ) : ℤ) ^ 2) := by
    nlinarith
  exact_mod_cast cast_bound

end Erdos336.Problem336
