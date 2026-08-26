import ErdosProblems.Erdos394.LargePrimeProductEmbedding

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary floor bounds for moving-modulus parameters
-/

open Nat Finset

namespace Erdos394

/-- If `a` is at least twice a positive divisor scale `d`, then the floor
`a/d` is at least the real half-quotient `a/(2d)`. -/
theorem half_real_div_le_cast_nat_div
    {a d : ℕ} (hd : 0 < d) (h2d : 2 * d ≤ a) :
    (a : ℝ) / (2 * (d : ℝ)) ≤ ((a / d : ℕ) : ℝ) := by
  let v := a / d
  have hv1 : 1 ≤ v := by
    dsimp [v]
    exact (Nat.le_div_iff_mul_le hd).2 (by omega)
  have halt : a < d * (v + 1) := by
    dsimp [v]
    exact Nat.lt_mul_div_succ a hd
  have hvsum : v + 1 ≤ 2 * v := by omega
  have hmul : d * (v + 1) ≤ d * (2 * v) :=
    Nat.mul_le_mul_left d hvsum
  have ha : a ≤ 2 * d * v := by
    calc
      a ≤ d * (v + 1) := halt.le
      _ ≤ d * (2 * v) := hmul
      _ = 2 * d * v := by ring
  have haR : (a : ℝ) ≤ (2 * (d : ℝ)) * (v : ℝ) := by
    exact_mod_cast ha
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using haR

/-- The canonical shifted-root horizon has the expected lower scale. -/
theorem horizon_floor_lower
    (K C0 q r : ℕ) (hK : 0 < K) (hC0 : 0 < C0)
    (hlarge : 2 * (C0 * K ^ (r + 1)) ≤ q) :
    (q : ℝ) / (2 * ((C0 * K ^ (r + 1) : ℕ) : ℝ)) ≤
      ((q / (C0 * K ^ (r + 1)) : ℕ) : ℝ) := by
  apply half_real_div_le_cast_nat_div
  · exact mul_pos hC0 (pow_pos hK _)
  · exact hlarge

/-- The canonical large-prime block base `X/(32q)` is at least
`X/(64q)` in reals when `64q≤X`. -/
theorem primeBase_floor_lower
    (X q : ℕ) (hq : 0 < q) (hlarge : 64 * q ≤ X) :
    (X : ℝ) / (64 * (q : ℝ)) ≤ ((X / (32 * q) : ℕ) : ℝ) := by
  have hd : 0 < 32 * q := mul_pos (by omega) hq
  have h2 : 2 * (32 * q) ≤ X := by
    calc
      2 * (32 * q) = 64 * q := by ring
      _ ≤ X := hlarge
  have h := half_real_div_le_cast_nat_div hd h2
  have hden : (2 : ℝ) * ((32 * q : ℕ) : ℝ) = 64 * (q : ℝ) := by
    push_cast
    ring
  rw [hden] at h
  exact h

/-- Every prime in the block above `N=X/(32q)` produces a represented integer
at most `X`. -/
theorem primeBlock_mul_modulus_le
    (X q ell : ℕ) (hell : ell ≤ 16 * (X / (32 * q))) :
    ell * q ≤ X := by
  calc
    ell * q ≤ (16 * (X / (32 * q))) * q := Nat.mul_le_mul_right q hell
    _ ≤ X := by
      have hdiv := Nat.div_mul_le_self X (32 * q)
      nlinarith

end Erdos394
