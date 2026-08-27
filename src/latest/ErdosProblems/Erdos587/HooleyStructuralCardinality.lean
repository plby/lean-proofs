import ErdosProblems.Erdos587.NVDevelopment

/-! # The full-dimensional subset-sum cardinality estimate excludes rank three -/

namespace Erdos587.CFP

theorem delta_rank_le_two_of_cardinality {m F C N r d V : ℕ}
    (hm : 0 < m) (hF : 0 < F) (hr : r ≤ d)
    (hcard : m ^ (r + 1) ≤ 2 * F ^ r * V) (hV : V ≤ C * m * N)
    (hlarge : 2 * F ^ d * C * N < m ^ 3) : r ≤ 2 := by
  by_contra hnot
  have hr3 : 3 ≤ r := by omega
  have hpower : m ^ 4 ≤ m ^ (r + 1) := Nat.pow_le_pow_right hm (by omega)
  have hFpower : F ^ r ≤ F ^ d := Nat.pow_le_pow_right hF hr
  have hbound : m ^ 4 ≤ (2 * F ^ d * C * N) * m := by
    calc
      _ ≤ 2 * F ^ r * V := hpower.trans hcard
      _ ≤ 2 * F ^ d * (C * m * N) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hFpower) hV
      _ = _ := by ring
  have hstrict : (2 * F ^ d * C * N) * m < m ^ 4 := by
    calc
      _ < m ^ 3 * m := Nat.mul_lt_mul_of_pos_right hlarge hm
      _ = m ^ 4 := (pow_succ m 3).symm
  omega

end Erdos587.CFP
