import ErdosProblems.Erdos69.PatternCoefficients
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Integer parameter hierarchy

All cutoffs are integer powers, so no floor or ceiling approximation enters
the moment comparison. Write `N = 36^m`, `B = N^4`. We retain `2*B` terms
after the initial `6*m` cancellations, use `y = 2^(2^B)` as the small-prime
cutoff, and average over `T = y^(40*B)` progression indices. The intermediate
cutoff is exactly the square root `R = y^(20*B)`.

This choice makes the pointwise omitted tail small: its logarithmic size is
of order `B*2^B`, whereas its binary denominator contains `2^(2*B)`.
-/

namespace Erdos69.Elementary

def patternSize (m : ℕ) : ℕ := 36 ^ m
def fluctuationScale (m : ℕ) : ℕ := patternSize m ^ 4
def dilationPrimeCutoff (m : ℕ) : ℕ := 2 ^ (patternSize m ^ 2)
def excludedPrimeCutoff (m : ℕ) : ℕ := 2 ^ (patternSize m ^ 3)
def retainedLength (m : ℕ) : ℕ := 2 * fluctuationScale m
def smallPrimeCutoff (m : ℕ) : ℕ := 2 ^ (2 ^ fluctuationScale m)
def progressionLength (m : ℕ) : ℕ := smallPrimeCutoff m ^ (40 * fluctuationScale m)
def intermediatePrimeCutoff (m : ℕ) : ℕ := smallPrimeCutoff m ^ (20 * fluctuationScale m)
def momentOrder (m : ℕ) : ℕ := 2 * fluctuationScale m

theorem patternSize_pos (m : ℕ) : 0 < patternSize m := by unfold patternSize; positivity
theorem fluctuationScale_pos (m : ℕ) : 0 < fluctuationScale m :=
  Nat.pow_pos (patternSize_pos m)
theorem dilationPrimeCutoff_pos (m : ℕ) : 0 < dilationPrimeCutoff m := by
  unfold dilationPrimeCutoff; positivity
theorem smallPrimeCutoff_pos (m : ℕ) : 0 < smallPrimeCutoff m := by
  unfold smallPrimeCutoff; positivity
theorem progressionLength_pos (m : ℕ) : 0 < progressionLength m :=
  Nat.pow_pos (smallPrimeCutoff_pos m)
theorem retainedLength_pos (m : ℕ) : 0 < retainedLength m :=
  Nat.mul_pos (by norm_num) (fluctuationScale_pos m)
theorem momentOrder_pos (m : ℕ) : 0 < momentOrder m := retainedLength_pos m
theorem momentOrder_even (m : ℕ) : Even (momentOrder m) := even_two_mul _

theorem initialLength_le_patternSize (m : ℕ) : 6 * m ≤ patternSize m := by
  induction m with
  | zero => simp [patternSize]
  | succ m ih =>
    have hp := patternSize_pos m
    have heq : patternSize (m + 1) = patternSize m * 36 := by simp [patternSize, pow_succ]
    rw [heq]
    omega

theorem digitRange_le_patternSize_square (m : ℕ) : 49 ^ m ≤ patternSize m ^ 2 := by
  have h : (49 : ℕ) ≤ 36 ^ 2 := by norm_num
  calc
    49 ^ m ≤ (36 ^ 2) ^ m := Nat.pow_le_pow_left h m
    _ = patternSize m ^ 2 := by
      simp only [patternSize, ← pow_mul]
      rw [Nat.mul_comm 2 m]

theorem digitRange_le_dilationPrimeCutoff (m : ℕ) : 49 ^ m ≤ dilationPrimeCutoff m := by
  exact (digitRange_le_patternSize_square m).trans Nat.lt_two_pow_self.le

theorem intermediatePrimeCutoff_square (m : ℕ) :
    intermediatePrimeCutoff m ^ 2 = progressionLength m := by
  unfold intermediatePrimeCutoff progressionLength
  rw [← pow_mul]
  congr 1
  omega

theorem smallPrimeCutoff_moment_ratio (m : ℕ) :
    progressionLength m = smallPrimeCutoff m ^ momentOrder m *
      smallPrimeCutoff m ^ (38 * fluctuationScale m) := by
  unfold progressionLength momentOrder
  rw [← pow_add]
  congr 1
  omega

end Erdos69.Elementary
