import ErdosProblems.Erdos421.MeanValuePowerStep
import ErdosProblems.Erdos421.MeanValueExponents

/-! # An unconditional iterated complete-system mean-value bound

All constants here are explicit natural numbers. The maximum in the recursion
covers the bounded range where residue-distinct prime selection does not apply.
-/

namespace Erdos421

def meanValueStepFactor (k r : ℕ) : ℕ :=
  (4 * k ^ 3 * k.factorial) *
    2 ^ ((2 * k ^ 3 + 1) * (2 * ((r + 1) * k) + meanValueTriangle k))

def meanValueSmallThreshold (k r : ℕ) : ℕ :=
  max ((4 * (((r + 2) * k) * ((r + 2) * k - 1))) ^ 2) (k ^ k)

def meanValueConstant (k : ℕ) : ℕ → ℕ
  | 0 => k.factorial
  | r + 1 => max (meanValueStepFactor k r * meanValueConstant k r)
      (meanValueSmallThreshold k r ^ (2 * ((r + 2) * k)))

theorem meanValueConstant_step_le (k r : ℕ) :
    meanValueStepFactor k r * meanValueConstant k r ≤ meanValueConstant k (r + 1) :=
  le_max_left _ _

theorem meanValueConstant_small_le (k r : ℕ) :
    meanValueSmallThreshold k r ^ (2 * ((r + 2) * k)) ≤ meanValueConstant k (r + 1) :=
  le_max_right _ _

theorem vinogradovCount_meanValueIteration {k : ℕ} (hk : 2 ≤ k) (r N : ℕ)
    (hN : 0 < N) :
    (vinogradovCount ((r + 1) * k) k N : ℝ) ≤
      meanValueConstant k r * (N : ℝ) ^ meanValueExponent k r := by
  have hkpos : 0 < k := by omega
  induction r generalizing N with
  | zero =>
    simpa only [zero_add, one_mul, meanValueConstant, meanValueExponent_zero,
      Real.rpow_natCast, Nat.cast_mul, Nat.cast_pow] using
      (Nat.cast_le.mpr (vinogradovCount_le_factorial (s := k) (k := k) (N := N) le_rfl) :
        (vinogradovCount k k N : ℝ) ≤ (k.factorial * N ^ k : ℕ))
  | succ r ih =>
    have hlength : k + (r + 1) * k = (r + 2) * k := by ring
    have hindex : (r + 1 + 1) * k = (r + 2) * k := by ring
    rw [hindex]
    by_cases hsmall : N ≤ meanValueSmallThreshold k r
    · have hcount : vinogradovCount ((r + 2) * k) k N ≤ meanValueConstant k (r + 1) :=
        (vinogradovCount_le_trivial _ _ _).trans
          ((Nat.pow_le_pow_left hsmall _).trans (meanValueConstant_small_le k r))
      have hone : 1 ≤ (N : ℝ) ^ meanValueExponent k (r + 1) :=
        Real.one_le_rpow (by exact_mod_cast hN) (meanValueExponent_nonneg hkpos _)
      exact (Nat.cast_le.mpr hcount).trans
        (le_mul_of_one_le_right (Nat.cast_nonneg _) hone)
    · have hlarge : meanValueSmallThreshold k r < N := Nat.lt_of_not_ge hsmall
      have hthreshold : (4 * ((k + (r + 1) * k) * (k + (r + 1) * k - 1))) ^ 2 < N := by
        rw [hlength]
        exact (le_max_left _ _).trans_lt hlarge
      have hkN : k ^ k ≤ N := ((le_max_right _ _).trans_lt hlarge).le
      have hexpUpper : meanValueExponent k r ≤
          (2 * ((r + 1) * k) + k * (k - 1) / 2 : ℕ) :=
        (meanValueExponent_le_moment hkpos r).trans (Nat.cast_le.mpr (Nat.le_add_right _ _))
      have hb := vinogradovCount_power_step hk (Nat.mul_pos (Nat.succ_pos r) hkpos)
        hthreshold hkN (Nat.cast_nonneg (meanValueConstant k r))
        (meanValueExponent_nonneg hkpos r) hexpUpper ih
      have heq := meanValueExponent_succ hkpos r
      dsimp only [meanValueTriangle] at heq
      rw [hlength, ← heq] at hb
      have hco : (4 * k ^ 3 * k.factorial : ℕ) *
          (2 : ℝ) ^ ((2 * k ^ 3 + 1) * (2 * ((r + 1) * k) + k * (k - 1) / 2)) *
            meanValueConstant k r ≤ (meanValueConstant k (r + 1) : ℝ) := by
        exact_mod_cast meanValueConstant_step_le k r
      exact hb.trans (mul_le_mul_of_nonneg_right hco (Real.rpow_nonneg (Nat.cast_nonneg N) _))

end Erdos421
