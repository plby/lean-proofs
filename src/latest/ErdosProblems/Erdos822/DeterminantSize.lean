/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.GoodDeterminantCharge
import ErdosProblems.Erdos822.ZeroDeterminant

/-! # Size and prime-tail control of a supported nonzero determinant -/

namespace Erdos822

open scoped BigOperators Classical

theorem reducedTotientDet_pos_of_odd_supported {N m m' : ℕ}
    (hN : 2 ≤ N) (hm : m ∈ oddRawCofactors N) (hm' : m' ∈ oddRawCofactors N)
    (hne : m ≠ m') (hsupport : (outerCollisionPairs (N ^ 60) m m').Nonempty) :
    0 < reducedTotientDet m m' := by
  have hφne : Nat.totient m ≠ Nat.totient m' := by
    intro hφ
    exact Finset.not_nonempty_empty (oddOuterCollisionPairs_eq_empty_of_totient_eq_of_ne hN hm hm' hφ hne ▸ hsupport)
  have hdelta : 0 < ((Nat.totient m : ℤ) - Nat.totient m').natAbs := by
    apply Int.natAbs_pos.mpr
    apply sub_ne_zero.mpr
    exact_mod_cast hφne
  have hgdiv := shiftedCoefficientGcd_dvd_totientNatAbs_of_nonempty
    (oddRawCofactors_pos hm) (oddRawCofactors_pos hm')
    (fun p hp ↦ oddOuterPrime_large_of_mem hN hm hp)
    (fun p hp ↦ oddOuterPrime_large_of_mem hN hm' hp) hsupport
  have hgpos : 0 < shiftedCoefficientGcd m m' := by
    apply Nat.pos_of_ne_zero
    apply Nat.gcd_ne_zero_right
    have hmpos := oddRawCofactors_pos hm'
    dsimp [shiftedTotient]
    omega
  exact Nat.div_pos (Nat.le_of_dvd hdelta hgdiv) hgpos

theorem reducedTotientDet_le_pow_twenty_eight {N m m' : ℕ}
    (hm : m ∈ oddRawCofactors N) (hm' : m' ∈ oddRawCofactors N) :
    reducedTotientDet m m' ≤ N ^ 28 := by
  exact (Nat.div_le_self _ _).trans (Int.natAbs_coe_sub_coe_le_of_le
    ((Nat.totient_le m).trans (oddRawCofactors_le_pow_twenty_eight hm))
    ((Nat.totient_le m').trans (oddRawCofactors_le_pow_twenty_eight hm')))

theorem natLog_le_fifty_six_mul_natLog {N H : ℕ} (hN : 2 ≤ N) (hH : H ≤ N ^ 28) :
    Nat.log 2 H ≤ 56 * Nat.log 2 N := by
  have hL : 1 ≤ Nat.log 2 N := Nat.log_pos (by norm_num) hN
  have hpow : N ^ 28 < 2 ^ ((Nat.log 2 N + 1) * 28) := by
    rw [pow_mul]
    exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by norm_num) N) (by norm_num)
  have hlog := (Nat.log_lt_of_lt_pow' (by omega) (hH.trans_lt hpow)).le
  omega

theorem sum_inv_primeTail_at_natLog_le_fifty_six {N H : ℕ}
    (hN : 2 ≤ N) (hHpos : 0 < H) (hH : H ≤ N ^ 28) :
    (∑ p ∈ primeFactorsAbove H (Nat.log 2 N), (1 : ℝ) / p) ≤ 56 := by
  have hL : 1 ≤ Nat.log 2 N := Nat.log_pos (by norm_num) hN
  have hLR : (0 : ℝ) < Nat.log 2 N := by exact_mod_cast hL
  have hlogR : (Nat.log 2 H : ℝ) ≤ 56 * (Nat.log 2 N : ℝ) :=
    by exact_mod_cast natLog_le_fifty_six_mul_natLog hN hH
  exact (sum_inv_primeFactorsAbove_le_log_div hHpos hL).trans ((div_le_iff₀ hLR).mpr hlogR)

theorem realLog_le_twice_natLog {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) ≤ 2 * (Nat.log 2 n : ℝ) := by
  have hL : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hlog := Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
    (show (n : ℝ) ≤ 2 ^ (Nat.log 2 n + 1) by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).le)
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hLR : (1 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hL
  nlinarith only [hlog, hlog2, hLR]

#print axioms reducedTotientDet_pos_of_odd_supported
#print axioms sum_inv_primeTail_at_natLog_le_fifty_six

end Erdos822
