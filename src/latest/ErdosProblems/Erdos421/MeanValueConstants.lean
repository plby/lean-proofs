import ErdosProblems.Erdos421.MeanValueIteration

/-! # Polynomial control of the logarithm of the iteration constant -/

namespace Erdos421

def meanValueCoefficient (k : ℕ) : ℕ :=
  (2 + 3 * k + k ^ 2) + (2 * k ^ 3 + 1) * (2 * k + k ^ 2) +
    (4 + 4 * k + k ^ 2) * (2 * k) + 1

theorem meanValueCoefficient_le_polynomial (k : ℕ) :
    meanValueCoefficient k ≤ 32 * (k + 1) ^ 5 := by
  dsimp only [meanValueCoefficient]
  ring_nf
  omega

theorem nat_factorial_le_two_pow_square (k : ℕ) : k.factorial ≤ 2 ^ (k ^ 2) := by
  calc
    _ ≤ k ^ k := Nat.factorial_le_pow k
    _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := k)).le k
    _ = _ := by rw [← pow_mul, pow_two]

theorem meanValueStepFactor_le_two_pow (k r : ℕ) :
    meanValueStepFactor k r ≤ 2 ^ (meanValueCoefficient k * (r + 1)) := by
  let P := 2 + 3 * k + k ^ 2
  let F := 2 * k ^ 3 + 1
  let a := 2 * ((r + 1) * k) + meanValueTriangle k
  have hfront : 4 * k ^ 3 * k.factorial ≤ 2 ^ P := by
    calc
      _ ≤ 4 * (2 ^ k) ^ 3 * 2 ^ (k ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4
          (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := k)).le 3))
          (nat_factorial_le_two_pow_square k)
      _ = _ := by
        change 2 ^ 2 * (2 ^ k) ^ 3 * 2 ^ (k ^ 2) = 2 ^ (2 + 3 * k + k ^ 2)
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
  have ha : a ≤ (r + 1) * (2 * k + k ^ 2) := by
    have ht := meanValueTriangle_le_square k
    have hs : k ^ 2 ≤ (r + 1) * k ^ 2 := by nlinarith
    dsimp only [a]
    nlinarith
  have he : P + F * a ≤ meanValueCoefficient k * (r + 1) := by
    calc
      _ ≤ P * (r + 1) + F * ((r + 1) * (2 * k + k ^ 2)) :=
        Nat.add_le_add (by nlinarith) (Nat.mul_le_mul_left F ha)
      _ = (P + F * (2 * k + k ^ 2)) * (r + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right (r + 1) (by dsimp [P, F, meanValueCoefficient]; omega)
  calc
    _ ≤ 2 ^ P * 2 ^ (F * a) := Nat.mul_le_mul_right _ hfront
    _ = 2 ^ (P + F * a) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

theorem meanValueSmallThreshold_le_two_pow (k r : ℕ) :
    meanValueSmallThreshold k r ≤ 2 ^ ((r + 2) * (4 + 4 * k + k ^ 2)) := by
  let L := (r + 2) * k
  have hfirst : (4 * (L * (L - 1))) ^ 2 ≤ 2 ^ (4 + 4 * L) := by
    calc
      _ ≤ (4 * (L * L)) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left 4
          (Nat.mul_le_mul_left L (Nat.sub_le L 1))) 2
      _ ≤ (4 * (2 ^ L * 2 ^ L)) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left 4
          (Nat.mul_le_mul (Nat.lt_two_pow_self (n := L)).le (Nat.lt_two_pow_self (n := L)).le)) 2
      _ = _ := by
        change (2 ^ 2 * (2 ^ L * 2 ^ L)) ^ 2 = 2 ^ (4 + 4 * L)
        rw [← pow_add, ← pow_add, ← pow_mul]
        congr 1
        ring
  have hexp : 4 + 4 * L ≤ (r + 2) * (4 + 4 * k + k ^ 2) := by
    dsimp [L]
    nlinarith
  have hsecond : k ^ k ≤ 2 ^ (k ^ 2) := by
    calc
      _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := k)).le k
      _ = _ := by rw [← pow_mul, pow_two]
  have hexp2 : k ^ 2 ≤ (r + 2) * (4 + 4 * k + k ^ 2) := by nlinarith
  exact max_le (hfirst.trans (Nat.pow_le_pow_right (by decide) hexp))
    (hsecond.trans (Nat.pow_le_pow_right (by decide) hexp2))

theorem meanValueSmallPower_le_two_pow (k r : ℕ) :
    meanValueSmallThreshold k r ^ (2 * ((r + 2) * k)) ≤
      2 ^ (meanValueCoefficient k * (r + 2) ^ 3) := by
  have hcoeff : (4 + 4 * k + k ^ 2) * (2 * k) ≤ meanValueCoefficient k := by
    dsimp [meanValueCoefficient]
    omega
  have hpow : (r + 2) ^ 2 ≤ (r + 2) ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  calc
    _ ≤ (2 ^ ((r + 2) * (4 + 4 * k + k ^ 2))) ^ (2 * ((r + 2) * k)) :=
      Nat.pow_le_pow_left (meanValueSmallThreshold_le_two_pow k r) _
    _ = 2 ^ (((4 + 4 * k + k ^ 2) * (2 * k)) * (r + 2) ^ 2) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hcoeff hpow)

theorem meanValueConstant_le_two_pow (k r : ℕ) :
    meanValueConstant k r ≤ 2 ^ (meanValueCoefficient k * (r + 1) ^ 3) := by
  induction r with
  | zero =>
    simp only [meanValueConstant, zero_add, one_pow, mul_one]
    refine (nat_factorial_le_two_pow_square k).trans (Nat.pow_le_pow_right (by decide) ?_)
    dsimp [meanValueCoefficient]
    omega
  | succ r ih =>
    apply max_le
    · calc
        _ ≤ 2 ^ (meanValueCoefficient k * (r + 1)) *
            2 ^ (meanValueCoefficient k * (r + 1) ^ 3) :=
          Nat.mul_le_mul (meanValueStepFactor_le_two_pow k r) ih
        _ = 2 ^ (meanValueCoefficient k * ((r + 1) + (r + 1) ^ 3)) := by
          rw [← pow_add]
          congr 1
          ring
        _ ≤ _ := Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul_left _ (by nlinarith : (r + 1) + (r + 1) ^ 3 ≤ (r + 1 + 1) ^ 3))
    · simpa only [Nat.add_assoc] using meanValueSmallPower_le_two_pow k r

end Erdos421
