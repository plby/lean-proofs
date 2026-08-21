import ErdosProblems.Erdos239.External.Erdos67.MRGSA10GlobalWindowExact
import ErdosProblems.Erdos239.External.Erdos67.MRShiuShiftedEuler

/-!
# The multiplicative Shiu weight for the A.10 low/high split

The source secondary sums are majorized by a single nonnegative
multiplicative function: retain the complete prime power above `y`, and
shift it by `eta`.  This file records the arithmetic of that weight before
the actual A.10 coefficient comparison.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

theorem primeBandPart_mul
    (P : ℕ → Prop) [DecidablePred P]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    primeBandPart P (m * n) = primeBandPart P m * primeBandPart P n := by
  apply Nat.eq_of_factorization_eq
    (primeBandPart_ne_zero P (m * n))
    (Nat.mul_ne_zero (primeBandPart_ne_zero P m)
      (primeBandPart_ne_zero P n))
  intro p
  rw [primeBandPart_factorization, Nat.factorization_mul hm.ne' hn.ne',
    Finsupp.filter_add,
    Nat.factorization_mul (primeBandPart_ne_zero P m)
      (primeBandPart_ne_zero P n), primeBandPart_factorization,
    primeBandPart_factorization]

theorem primeBandPart_one (P : ℕ → Prop) [DecidablePred P] :
    primeBandPart P 1 = 1 := by
  apply Nat.eq_of_factorization_eq (primeBandPart_ne_zero P 1) one_ne_zero
  intro p
  rw [primeBandPart_factorization]
  simp [Finsupp.filter_apply]

theorem primeBandPart_prime
    (P : ℕ → Prop) [DecidablePred P]
    {p : ℕ} (hp : p.Prime) :
    primeBandPart P p = if P p then p else 1 := by
  apply Nat.eq_of_factorization_eq (primeBandPart_ne_zero P p) (by
    split <;> simp [hp.ne_zero])
  intro q
  rw [primeBandPart_factorization, hp.factorization]
  by_cases hP : P p
  · simp [hP, hp.factorization]
  · simp [hP]

theorem primeBandPart_prime_pow
    (P : ℕ → Prop) [DecidablePred P]
    {p k : ℕ} (hp : p.Prime) :
    primeBandPart P (p ^ k) = if P p then p ^ k else 1 := by
  apply Nat.eq_of_factorization_eq (primeBandPart_ne_zero P (p ^ k)) (by
    split <;> simp [hp.ne_zero])
  intro q
  rw [primeBandPart_factorization, hp.factorization_pow]
  by_cases hP : P p
  · simp [hP, hp.factorization_pow]
  · simp [hP]

/-- The low/high Shiu majorant.  Its value at zero is immaterial to the
positive prefix but chosen to fit the global HR theorem exactly. -/
def gsA10ShiuWeight (y : ℕ) (eta : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    (primeBandPart (fun p ↦ ¬ p ≤ y) n : ℝ) ^ (-eta)

@[simp] theorem gsA10ShiuWeight_zero (y : ℕ) (eta : ℝ) :
    gsA10ShiuWeight y eta 0 = 0 := by simp [gsA10ShiuWeight]

@[simp] theorem gsA10ShiuWeight_one (y : ℕ) (eta : ℝ) :
    gsA10ShiuWeight y eta 1 = 1 := by
  simp [gsA10ShiuWeight, primeBandPart_one]

theorem gsA10ShiuWeight_nonneg (y : ℕ) (eta : ℝ) (n : ℕ) :
    0 ≤ gsA10ShiuWeight y eta n := by
  unfold gsA10ShiuWeight
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem gsA10ShiuWeight_mul
    (y : ℕ) (eta : ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    gsA10ShiuWeight y eta (m * n) =
      gsA10ShiuWeight y eta m * gsA10ShiuWeight y eta n := by
  rw [gsA10ShiuWeight, if_neg (Nat.mul_ne_zero hm.ne' hn.ne'),
    gsA10ShiuWeight, if_neg hm.ne', gsA10ShiuWeight, if_neg hn.ne',
    primeBandPart_mul (fun p ↦ ¬ p ≤ y) hm hn, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

theorem gsA10ShiuWeight_prime
    (y : ℕ) (eta : ℝ) {p : ℕ} (hp : p.Prime) :
    gsA10ShiuWeight y eta p =
      if p ≤ y then 1 else (p : ℝ) ^ (-eta) := by
  rw [gsA10ShiuWeight, if_neg hp.ne_zero,
    primeBandPart_prime (fun q ↦ ¬ q ≤ y) hp]
  by_cases hpy : p ≤ y
  · simp [hpy]
  · simp [hpy]

theorem gsA10ShiuWeight_primePower_le_one
    {y : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (p : ℕ) (hp : p.Prime) (j : ℕ) :
    gsA10ShiuWeight y eta (p ^ (j + 1)) ≤ 1 := by
  have hpowpos : 0 < p ^ (j + 1) := pow_pos hp.pos _
  rw [gsA10ShiuWeight, if_neg hpowpos.ne',
    primeBandPart_prime_pow (fun q ↦ ¬ q ≤ y) hp]
  by_cases hpy : p ≤ y
  · simp [hpy]
  · simp only [hpy, not_false_eq_true, if_true, Nat.cast_pow]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (Nat.one_le_pow (j + 1) p hp.pos))
      (neg_nonpos.mpr heta)

/-- Increasing the high-prime shift decreases the Shiu weight pointwise. -/
theorem gsA10ShiuWeight_antitone_shift
    (y n : ℕ) {sigma rho : ℝ} (h : sigma ≤ rho) :
    gsA10ShiuWeight y rho n ≤ gsA10ShiuWeight y sigma n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [gsA10ShiuWeight, if_neg hn, gsA10ShiuWeight, if_neg hn]
  have hpart : (1 : ℝ) ≤
      primeBandPart (fun p ↦ ¬ p ≤ y) n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (primeBandPart_ne_zero (fun p ↦ ¬ p ≤ y) n)
  exact Real.rpow_le_rpow_of_exponent_le hpart (by linarith)

end

end Erdos67.MRHalaszBands
