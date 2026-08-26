import Mathlib.Data.Nat.Choose.Central

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos1188

/-- A convenient exponential lower bound for central binomial coefficients. -/
theorem two_pow_lt_choose_two_mul (k : ℕ) (hk : 4 ≤ k) :
    2 ^ k < (2 * k).choose k := by
  have hcentral := Nat.four_pow_lt_mul_centralBinom k hk
  have hkpow : k ≤ 2 ^ k := by
    exact le_trans (Nat.le_mul_of_pos_left k (by decide : 0 < 2))
      (Nat.mul_le_pow (by decide : (2 : ℕ) ≠ 1) k)
  have hmul : 2 ^ k * 2 ^ k < 2 ^ k * Nat.centralBinom k := by
    calc
      2 ^ k * 2 ^ k = 4 ^ k := by
        rw [← mul_pow]
        norm_num
      _ < k * Nat.centralBinom k := hcentral
      _ ≤ 2 ^ k * Nat.centralBinom k := Nat.mul_le_mul_right _ hkpow
  have := Nat.lt_of_mul_lt_mul_left hmul
  simpa [Nat.centralBinom, Nat.mul_comm] using this

/-- If `k` lies below half of `N`, then the `k`th binomial coefficient of `N`
is at least `2^k`. -/
theorem two_pow_le_choose_of_two_mul_le (N k : ℕ) (hk : 4 ≤ k)
    (h2k : 2 * k ≤ N) :
    2 ^ k ≤ N.choose k := by
  exact le_trans (two_pow_lt_choose_two_mul k hk).le
    (Nat.choose_le_choose k h2k)

/-- Quantitative lower bound for the descending factorial arising from a
Bertrand prime between one quarter and one half of `2^m`. -/
theorem two_pow_mul_le_descFactorial (m P : ℕ) (hm : 2 ≤ m)
    (hlo : 2 ^ (m - 2) < P) (hhi : P ≤ 2 ^ (m - 1)) :
    2 ^ ((m - 1) * 2 ^ (m - 2)) ≤
      (2 ^ m - 1).descFactorial (P - 1) := by
  let t := 2 ^ (m - 2)
  let b := (2 ^ m - 1) + 1 - (P - 1)
  have ht : t ≤ P - 1 := by simp only [t]; omega
  have hpowm : 2 ^ m = 2 * 2 ^ (m - 1) := by
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (m - 1) := Nat.mul_comm _ _
  have hb : 2 ^ (m - 1) ≤ b := by
    simp only [b]
    rw [Nat.sub_add_cancel (Nat.one_le_pow m 2 (by decide)), hpowm]
    omega
  rw [pow_mul]
  change (2 ^ (m - 1)) ^ t ≤ (2 ^ m - 1).descFactorial (P - 1)
  have hExp : (2 ^ (m - 1)) ^ t ≤ (2 ^ (m - 1)) ^ (P - 1) :=
    Nat.pow_le_pow_right (by positivity) ht
  have hBase : (2 ^ (m - 1)) ^ (P - 1) ≤ b ^ (P - 1) :=
    Nat.pow_le_pow_left hb _
  have hDesc : b ^ (P - 1) ≤ (2 ^ m - 1).descFactorial (P - 1) := by
    exact Nat.pow_sub_le_descFactorial (2 ^ m - 1) (P - 1)
  exact hExp.trans (hBase.trans hDesc)

end Erdos1188
