/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.OffDiagonalMoment
import ErdosProblems.Erdos387.SubpowerReciprocalEnergy

/-!
# Off-diagonal reciprocal moments on the subpower scale

This file specializes the rough-divisor estimate for nonzero cleared
reciprocal numerators to the power-of-two scales used in the Erdős 387
development.  The two depths below separately control the size of the
rough-divisor code and the number of its possible prime coordinates.
-/

namespace Erdos387

open Filter

namespace SubpowerScale

/-- Depth used to encode a divisor of a cleared `2 * ell`-variable
reciprocal numerator by primes at least `z`. -/
def modularMomentDepth (N ell : ℕ) : ℕ :=
  4 * (ell + 1) * N ^ 2

/-- Binary exponent bounding every nonzero cleared numerator in the
medium coordinate box. -/
def binaryMomentDepth (N k ell : ℕ) : ℕ :=
  comparableUpperLog N k * (2 * ell) + N ^ 2

/-- Fixed coefficient in the elementary polynomial upper bound for the
binary numerator exponent. -/
def binaryMomentCoefficient (k ell : ℕ) : ℕ :=
  BPZScale.mediumExp k * (2 * ell) + 2

/-- Fixed slope of a power-of-two envelope for `binaryMomentDepth + 1`. -/
def binaryMomentSlope (k ell : ℕ) : ℕ :=
  (Nat.log 2 (binaryMomentCoefficient k ell) + 1) + (2 * k + 5)

theorem four_mul_lt_two_pow_square
    {N ell : ℕ} (hN : 1 ≤ N) (hell : 4 * ell ≤ N) :
    4 * ell < 2 ^ (N ^ 2) := by
  calc
    4 * ell ≤ N := hell
    _ < 2 ^ N := Nat.lt_two_pow_self
    _ ≤ 2 ^ (N ^ 2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith

theorem medium_numerator_lt_two_pow_binaryMomentDepth
    {N k ell : ℕ} (hN : 1 ≤ N) (hell : 4 * ell ≤ N) :
    4 * ell * medium N k ^ (2 * ell) <
      2 ^ (binaryMomentDepth N k ell + 1) := by
  have hcoeff := four_mul_lt_two_pow_square hN hell
  rw [medium_eq_pow_two, ← pow_mul]
  have hmul := Nat.mul_lt_mul_of_pos_right hcoeff
    (pow_pos (by norm_num : 0 < 2) (comparableUpperLog N k * (2 * ell)))
  calc
    4 * ell * 2 ^ (comparableUpperLog N k * (2 * ell)) <
        2 ^ (N ^ 2) * 2 ^ (comparableUpperLog N k * (2 * ell)) := hmul
    _ = 2 ^ binaryMomentDepth N k ell := by
      rw [← pow_add]
      unfold binaryMomentDepth
      congr 1
      omega
    _ < 2 ^ (binaryMomentDepth N k ell + 1) := by
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr (by omega)

theorem medium_numerator_lt_z_pow_modularMomentDepth
    {N k ell : ℕ} (hN : 1 ≤ N) (hk : 0 < k)
    (hell : 4 * ell ≤ N) :
    4 * ell * medium N k ^ (2 * ell) <
      z N k ^ (modularMomentDepth N ell + 1) := by
  have hcoeff := four_mul_lt_two_pow_square hN hell
  have hupper := comparableUpperLog_le_roughPower_mul_square N k
  have hrough : 1 ≤ roughPower N k := by
    exact roughPower_pos (by omega) hk
  have hExp :
      N ^ 2 + comparableUpperLog N k * (2 * ell) ≤
        roughPower N k * modularMomentDepth N ell := by
    calc
      N ^ 2 + comparableUpperLog N k * (2 * ell) ≤
          roughPower N k * N ^ 2 +
            (roughPower N k * N ^ 2) * (2 * ell) := by
        apply Nat.add_le_add
        · simpa using Nat.mul_le_mul_right (N ^ 2) hrough
        · exact Nat.mul_le_mul_right (2 * ell) hupper
      _ = roughPower N k * ((2 * ell + 1) * N ^ 2) := by ring
      _ ≤ roughPower N k * modularMomentDepth N ell := by
        apply Nat.mul_le_mul_left
        unfold modularMomentDepth
        nlinarith
  rw [medium_eq_pow_two, ← pow_mul, z, ← pow_mul]
  have hmul := Nat.mul_lt_mul_of_pos_right hcoeff
    (pow_pos (by norm_num : 0 < 2) (comparableUpperLog N k * (2 * ell)))
  calc
    4 * ell * 2 ^ (comparableUpperLog N k * (2 * ell)) <
        2 ^ (N ^ 2) * 2 ^ (comparableUpperLog N k * (2 * ell)) := hmul
    _ = 2 ^ (N ^ 2 + comparableUpperLog N k * (2 * ell)) := by
      rw [pow_add]
    _ ≤ 2 ^ (roughPower N k * modularMomentDepth N ell) := by
      exact Nat.pow_le_pow_right (by norm_num) hExp
    _ < 2 ^ (roughPower N k * (modularMomentDepth N ell + 1)) := by
      apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr
      nlinarith

theorem binaryMomentDepth_succ_le_coefficient_mul_scalePower
    {N k ell : ℕ} (hN : 1 ≤ N) :
    binaryMomentDepth N k ell + 1 ≤
      binaryMomentCoefficient k ell * scalePower N k := by
  have hSquare : N ^ 2 ≤ scalePower N k := by
    unfold scalePower
    exact Nat.pow_le_pow_right hN (by omega)
  have hScaleOne : 1 ≤ scalePower N k := by
    unfold scalePower
    exact one_le_pow₀ (by omega)
  unfold binaryMomentDepth comparableUpperLog binaryMomentCoefficient
  calc
    scalePower N k * BPZScale.mediumExp k * (2 * ell) + N ^ 2 + 1 =
        (BPZScale.mediumExp k * (2 * ell)) * scalePower N k +
          N ^ 2 + 1 := by ring
    _ ≤ (BPZScale.mediumExp k * (2 * ell)) * scalePower N k +
          scalePower N k + scalePower N k := by omega
    _ = (BPZScale.mediumExp k * (2 * ell) + 2) * scalePower N k := by
      ring

theorem binaryMomentDepth_succ_le_two_pow_slope
    {N k ell : ℕ} (hN : 1 ≤ N) :
    binaryMomentDepth N k ell + 1 ≤
      2 ^ (binaryMomentSlope k ell * N) := by
  let C := binaryMomentCoefficient k ell
  let q := Nat.log 2 C + 1
  let e := 2 * k + 5
  have hC : C ≤ 2 ^ q := by
    dsimp [q]
    exact (Nat.lt_pow_succ_log_self (by norm_num) C).le
  have hNtwo : N ≤ 2 ^ N := Nat.lt_two_pow_self.le
  have hNPow : N ^ e ≤ (2 ^ N) ^ e := Nat.pow_le_pow_left hNtwo e
  have hqN : q ≤ q * N := by
    simpa using Nat.mul_le_mul_left q hN
  calc
    binaryMomentDepth N k ell + 1 ≤
        C * scalePower N k := by
      simpa [C] using
        binaryMomentDepth_succ_le_coefficient_mul_scalePower
          (N := N) (k := k) (ell := ell) hN
    _ = C * N ^ e := by rfl
    _ ≤ 2 ^ q * (2 ^ N) ^ e := Nat.mul_le_mul hC hNPow
    _ = 2 ^ (q + N * e) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((q + e) * N) := by
      apply Nat.pow_le_pow_right (by norm_num)
      calc
        q + N * e ≤ q * N + N * e := Nat.add_le_add_right hqN _
        _ = (q + e) * N := by ring
    _ = 2 ^ (binaryMomentSlope k ell * N) := by
      rfl

/-- A direct finite threshold after which the off-diagonal divisor-code
overhead fits inside one copy of `base`. -/
theorem momentDivisorOverhead_le_base
    {N k ell : ℕ}
    (hN : max 1 (4 * binaryMomentSlope k ell * (ell + 1)) ≤ N) :
    (binaryMomentDepth N k ell + 1) ^ modularMomentDepth N ell ≤
      base N k := by
  let S := binaryMomentSlope k ell
  let C := 4 * S * (ell + 1)
  have hNone : 1 ≤ N := (le_max_left 1 C).trans hN
  have hCN : C ≤ N := (le_max_right 1 C).trans hN
  have hP := binaryMomentDepth_succ_le_two_pow_slope
    (N := N) (k := k) (ell := ell) hNone
  have hExp : S * N * modularMomentDepth N ell ≤ scalePower N k := by
    calc
      S * N * modularMomentDepth N ell = C * N ^ 3 := by
        dsimp [C, modularMomentDepth]
        ring
      _ ≤ N * N ^ 3 := Nat.mul_le_mul_right (N ^ 3) hCN
      _ = N ^ 4 := by ring
      _ ≤ N ^ (2 * k + 5) :=
        Nat.pow_le_pow_right hNone (by omega)
      _ = scalePower N k := by rfl
  calc
    (binaryMomentDepth N k ell + 1) ^ modularMomentDepth N ell ≤
        (2 ^ (S * N)) ^ modularMomentDepth N ell := by
      apply Nat.pow_le_pow_left
      simpa [S] using hP
    _ = 2 ^ (S * N * modularMomentDepth N ell) := by rw [← pow_mul]
    _ ≤ 2 ^ scalePower N k := Nat.pow_le_pow_right (by norm_num) hExp
    _ = base N k := by rfl

theorem eventually_momentDivisorOverhead_le_base
    (k ell : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (binaryMomentDepth N k ell + 1) ^ modularMomentDepth N ell ≤
        base N k := by
  filter_upwards [eventually_ge_atTop
    (max 1 (4 * binaryMomentSlope k ell * (ell + 1)))] with N hN
  exact momentDivisorOverhead_le_base hN

/-- The generic off-diagonal modular-energy estimate, now with every
numerator-size and prime-factor-count side condition discharged by the
subpower scale. -/
theorem offDiagonalModulusTuples_card_le_medium
    {ell N k : ℕ} (hN : 1 ≤ N) (hk : 0 < k)
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset (Fin ell ⊕ Fin ell)) (U : Finset ℕ)
    (hell : 4 * ell ≤ N)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (z N k) d)
    (hUcop : ∀ d ∈ Q, ∀ u ∈ U, u.Coprime (modulus d))
    (hUle : ∀ u ∈ U, u ≤ medium N k) :
    (ReciprocalMoment.offDiagonalModulusTuples Q modulus A U).card ≤
      U.card ^ (2 * ell) *
        (binaryMomentDepth N k ell + 1) ^ modularMomentDepth N ell := by
  have hz : 1 < z N k := two_le_z (by omega) hk
  have hT : 1 ≤ medium N k := by
    rw [medium_eq_pow_two]
    exact one_le_pow₀ (by norm_num)
  have hcard : Fintype.card (Fin ell ⊕ Fin ell) = 2 * ell := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hZPow :
      2 * Fintype.card (Fin ell ⊕ Fin ell) *
          medium N k ^ Fintype.card (Fin ell ⊕ Fin ell) <
        z N k ^ (modularMomentDepth N ell + 1) := by
    simpa [hcard, show 2 * (2 * ell) = 4 * ell by ring] using
      medium_numerator_lt_z_pow_modularMomentDepth hN hk hell
  have hTwoPow :
      2 * Fintype.card (Fin ell ⊕ Fin ell) *
          medium N k ^ Fintype.card (Fin ell ⊕ Fin ell) <
        2 ^ (binaryMomentDepth N k ell + 1) := by
    simpa [hcard, show 2 * (2 * ell) = 4 * ell by ring] using
      medium_numerator_lt_two_pow_binaryMomentDepth hN hell
  simpa [show ell + ell = 2 * ell by omega] using
    (ReciprocalMoment.offDiagonalModulusTuples_card_le_of_coordinate_bound
      Q modulus A U (L := modularMomentDepth N ell)
      (D := binaryMomentDepth N k ell) hz hT hDmod hQrough hUcop hUle
      hZPow hTwoPow)

/-- Final `coordinate box * base` form of the off-diagonal estimate. -/
theorem offDiagonalModulusTuples_card_le_medium_mul_base
    {ell N k : ℕ} (hk : 0 < k)
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset (Fin ell ⊕ Fin ell)) (U : Finset ℕ)
    (hN : max (4 * ell)
      (max 1 (4 * binaryMomentSlope k ell * (ell + 1))) ≤ N)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (z N k) d)
    (hUcop : ∀ d ∈ Q, ∀ u ∈ U, u.Coprime (modulus d))
    (hUle : ∀ u ∈ U, u ≤ medium N k) :
    (ReciprocalMoment.offDiagonalModulusTuples Q modulus A U).card ≤
      U.card ^ (2 * ell) * base N k := by
  have hell : 4 * ell ≤ N := (le_max_left _ _).trans hN
  have hthreshold :
      max 1 (4 * binaryMomentSlope k ell * (ell + 1)) ≤ N :=
    (le_max_right _ _).trans hN
  have hoff := offDiagonalModulusTuples_card_le_medium
    (N := N) (k := k) (ell := ell) (by omega) hk
      Q modulus A U hell hDmod hQrough hUcop hUle
  exact hoff.trans (Nat.mul_le_mul_left _
    (momentDivisorOverhead_le_base hthreshold))

end SubpowerScale

end Erdos387
