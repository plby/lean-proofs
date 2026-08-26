/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Tactic

/-! # Integer inequalities for the cycle Ramsey induction -/

namespace Erdos569

/-- The pigeonhole star has room for the first blue clique. -/
theorem first_neighborhood_room {k n m d D : ℕ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hdegree : n * d ≤ 2 * m)
    (hstar : (k - 1) * m + 1 - (n - 1) ≤ d * D) :
    (k - 2) * (n / 2) + 1 ≤ D := by
  have hhalf : 2 * (n / 2) ≤ n := by omega
  have hdhalf : d * (n / 2) ≤ m := by nlinarith
  have hlarge : (k - 2) * m + 2 ≤ d * D := by
    have hkm : (k - 1) * m = (k - 2) * m + m := by
      have he : k - 1 = k - 2 + 1 := by omega
      rw [he, Nat.add_mul, one_mul]
    omega
  by_contra h
  have hD : D ≤ (k - 2) * (n / 2) := by omega
  have hmul := Nat.mul_le_mul_left d hD
  have hmul' := Nat.mul_le_mul_left (k - 2) hdhalf
  nlinarith

end Erdos569
