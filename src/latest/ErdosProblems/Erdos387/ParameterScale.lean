/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.AlmostPrimeExhaustion

/-!
# An integral parameter scale for the BNPZ divisor estimates

Using powers of one natural parameter avoids all floor and real-power
rounding in the final specialization.  The exponents below represent exactly
`z = X^(3⁻ᵏ)`, the `101/300` and `101/200` thresholds, and the
`1/k^100`, `1/(2k)`, and `1/k^4` thresholds from the source.
-/

namespace Erdos387

namespace BPZScale

def xExp (k : ℕ) : ℕ := 600 * 3 ^ k * k ^ 100
def zExp (k : ℕ) : ℕ := 600 * k ^ 100
def yExp (k : ℕ) : ℕ := 600 * 3 ^ k
def mediumExp (k : ℕ) : ℕ := 202 * 3 ^ k * k ^ 100
def largeExp (k : ℕ) : ℕ := 303 * 3 ^ k * k ^ 100
def switchExp (k : ℕ) : ℕ := 297 * 3 ^ k * k ^ 100
def secondExp (k : ℕ) : ℕ := 300 * 3 ^ k * k ^ 99
def gapExp (k : ℕ) : ℕ := 600 * 3 ^ k * k ^ 96

def X (t k : ℕ) : ℕ := t ^ xExp k
def z (t k : ℕ) : ℕ := t ^ zExp k
def y (t k : ℕ) : ℕ := t ^ yExp k
def medium (t k : ℕ) : ℕ := t ^ mediumExp k
def large (t k : ℕ) : ℕ := t ^ largeExp k
def secondMin (t k : ℕ) : ℕ := t ^ secondExp k
def gap (t k : ℕ) : ℕ := t ^ gapExp k

theorem six_hundred_le_pow_99 {k : ℕ} (hk : 3 ≤ k) : 600 ≤ k ^ 99 := by
  calc
    600 ≤ 3 ^ 6 := by norm_num
    _ ≤ k ^ 6 := Nat.pow_le_pow_left hk 6
    _ ≤ k ^ 99 := Nat.pow_le_pow_right (by omega) (by omega)

theorem eighteen_hundred_mul_le_three_mul_pow_100 {k : ℕ}
    (hk : 3 ≤ k) : 1800 * k ≤ 3 * k ^ 100 := by
  have h600 := six_hundred_le_pow_99 hk
  calc
    1800 * k = 3 * (600 * k) := by ring
    _ ≤ 3 * (k ^ 99 * k) := by gcongr
    _ = 3 * k ^ 100 := by
      exact congrArg (fun n : ℕ => 3 * n) (pow_succ k 99).symm

theorem almostSecondExponent_lt {k : ℕ} (hk : 3 ≤ k) :
    3 * k * yExp k + mediumExp k + (k - 1) * secondExp k + 1 ≤
      xExp k := by
  let A := 3 ^ k
  let P := k ^ 100
  have hsmall : A * (1800 * k) ≤ A * (3 * P) := by
    exact Nat.mul_le_mul_left A
      (by simpa [P] using eighteen_hundred_mul_le_three_mul_pow_100 hk)
  have hkpow : (k - 1) * k ^ 99 ≤ P := by
    dsimp [P]
    calc
      (k - 1) * k ^ 99 ≤ k * k ^ 99 := by gcongr; omega
      _ = k ^ 100 := by
        calc
          k * k ^ 99 = k ^ 99 * k ^ 1 := by simp [mul_comm]
          _ = k ^ (99 + 1) := (pow_add k 99 1).symm
          _ = k ^ 100 := by norm_num
  have hsecond : A * (300 * ((k - 1) * k ^ 99)) ≤
      A * (300 * P) := by gcongr
  have hAP : 1 ≤ A * P := by
    have hpos : 0 < A * P := by
      apply Nat.mul_pos
      · exact pow_pos (by norm_num) _
      · exact pow_pos (by omega) _
    omega
  dsimp [xExp, yExp, mediumExp, secondExp, A, P] at *
  calc
    3 * k * (600 * 3 ^ k) + 202 * 3 ^ k * k ^ 100 +
          (k - 1) * (300 * 3 ^ k * k ^ 99) + 1 ≤
        505 * (3 ^ k * k ^ 100) + 1 := by
      nlinarith
    _ ≤ 600 * (3 ^ k * k ^ 100) := by omega
    _ = 600 * 3 ^ k * k ^ 100 := by ring

theorem almostGapExponent_lt {k : ℕ} (hk : 3 ≤ k) :
    3 * k * yExp k + k * (gapExp k + secondExp k) + 1 ≤ xExp k := by
  let A := 3 ^ k
  let P := k ^ 100
  have hsmall : A * (1800 * k) ≤ A * (3 * P) := by
    exact Nat.mul_le_mul_left A
      (by simpa [P] using eighteen_hundred_mul_le_three_mul_pow_100 hk)
  have hk2 : 3 ≤ k ^ 2 := by nlinarith [Nat.pow_le_pow_left hk 2]
  have hgapCore : 600 * k ^ 98 ≤ 200 * P := by
    dsimp [P]
    have hmul := Nat.mul_le_mul_left (200 * k ^ 98) hk2
    calc
      600 * k ^ 98 = (200 * k ^ 98) * 3 := by ring
      _ ≤ (200 * k ^ 98) * k ^ 2 := hmul
      _ = 200 * k ^ 100 := by
        rw [show k ^ 100 = k ^ 98 * k ^ 2 by
          simpa using pow_add k 98 2]
        ring
  have hgap : A * (600 * k ^ 98) ≤ A * (200 * P) := by gcongr
  have hAP : 1 ≤ A * P := by
    have hpos : 0 < A * P := by
      apply Nat.mul_pos
      · exact pow_pos (by norm_num) _
      · exact pow_pos (by omega) _
    omega
  dsimp [xExp, yExp, gapExp, secondExp, A, P] at *
  calc
    3 * k * (600 * 3 ^ k) +
          k * (600 * 3 ^ k * k ^ 96 + 300 * 3 ^ k * k ^ 99) + 1 ≤
        503 * (3 ^ k * k ^ 100) + 1 := by
      nlinarith
    _ ≤ 600 * (3 ^ k * k ^ 100) := by omega
    _ = 600 * 3 ^ k * k ^ 100 := by ring

theorem large_add_switch (k : ℕ) : largeExp k + switchExp k = xExp k := by
  simp only [largeExp, switchExp, xExp]
  ring

theorem twice_switchExponent_lt {k : ℕ} (hk : 3 ≤ k) :
    2 * switchExp k + 1 ≤ xExp k := by
  have hpos : 1 ≤ 3 ^ k * k ^ 100 := by
    have : 0 < 3 ^ k * k ^ 100 :=
      Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (by omega) _)
    omega
  simp only [switchExp, xExp]
  nlinarith

/-- Absorb a fixed coefficient into one extra power of the base, then divide
by two. -/
theorem coeff_mul_pow_le_half {t B e E : ℕ}
    (ht : 1 ≤ t) (hB : 2 * B ≤ t) (he : e + 1 ≤ E) :
    B * t ^ e ≤ t ^ E / 2 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  calc
    B * t ^ e * 2 = (2 * B) * t ^ e := by ac_rfl
    _ ≤ t * t ^ e := Nat.mul_le_mul_right _ hB
    _ = t ^ (e + 1) := by rw [pow_succ]; ac_rfl
    _ ≤ t ^ E := Nat.pow_le_pow_right ht he

theorem almostSecondProduct_eq (t B k : ℕ) :
    B * y t k ^ (3 * k) * medium t k * secondMin t k ^ (k - 1) =
      B * t ^
        (3 * k * yExp k + mediumExp k + (k - 1) * secondExp k) := by
  unfold y medium secondMin
  rw [← pow_mul, ← pow_mul]
  calc
    B * t ^ (yExp k * (3 * k)) * t ^ mediumExp k *
          t ^ (secondExp k * (k - 1)) =
        B * t ^ (yExp k * (3 * k) + mediumExp k +
          secondExp k * (k - 1)) := by
      rw [pow_add, pow_add]
      ring
    _ = _ := by
      congr 2
      ring

theorem almostGapProduct_eq (t B k : ℕ) :
    B * y t k ^ (3 * k) * (gap t k * secondMin t k) ^ k =
      B * t ^ (3 * k * yExp k + k * (gapExp k + secondExp k)) := by
  unfold y gap secondMin
  rw [← pow_add, ← pow_mul, ← pow_mul]
  calc
    B * t ^ (yExp k * (3 * k)) *
          t ^ ((gapExp k + secondExp k) * k) =
        B * t ^ (yExp k * (3 * k) +
          (gapExp k + secondExp k) * k) := by
      rw [pow_add]
      ring
    _ = _ := by
      congr 2
      ring

theorem almostSecond_scale {t B k : ℕ} (hk : 3 ≤ k)
    (ht : 1 ≤ t) (hB : 2 * B ≤ t) :
    B * y t k ^ (3 * k) * medium t k * secondMin t k ^ (k - 1) ≤
      X t k / 2 := by
  rw [almostSecondProduct_eq, X]
  exact coeff_mul_pow_le_half ht hB (almostSecondExponent_lt hk)

theorem almostGap_scale {t B k : ℕ} (hk : 3 ≤ k)
    (ht : 1 ≤ t) (hB : 2 * B ≤ t) :
    B * y t k ^ (3 * k) * (gap t k * secondMin t k) ^ k ≤
      X t k / 2 := by
  rw [almostGapProduct_eq, X]
  exact coeff_mul_pow_le_half ht hB (almostGapExponent_lt hk)

theorem X_div_large_succ_le_switchPow (t k : ℕ) :
    X t k / (large t k + 1) ≤ t ^ switchExp k := by
  apply Nat.div_le_of_le_mul
  calc
    X t k = t ^ switchExp k * t ^ largeExp k := by
      rw [X, ← pow_add]
      congr 1
      calc
        xExp k = largeExp k + switchExp k := (large_add_switch k).symm
        _ = switchExp k + largeExp k := by omega
    _ ≤ t ^ switchExp k * (t ^ largeExp k + 1) := by gcongr; omega
    _ = (large t k + 1) * t ^ switchExp k := by
      simp [large, mul_comm]

theorem large_switch_square_scale {t k : ℕ} (hk : 3 ≤ k) (ht : 2 ≤ t) :
    (X t k / (large t k + 1)) ^ 2 ≤ X t k / 2 := by
  have hdiv := X_div_large_succ_le_switchPow t k
  have hsq := Nat.pow_le_pow_left hdiv 2
  have hhalf : t ^ (2 * switchExp k) ≤ t ^ xExp k / 2 := by
    simpa using coeff_mul_pow_le_half (B := 1) (e := 2 * switchExp k)
      (E := xExp k) (by omega) (by omega) (twice_switchExponent_lt hk)
  calc
    (X t k / (large t k + 1)) ^ 2 ≤ (t ^ switchExp k) ^ 2 := hsq
    _ = t ^ (2 * switchExp k) := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ t ^ xExp k / 2 := hhalf
    _ = X t k / 2 := rfl

end BPZScale

end Erdos387
