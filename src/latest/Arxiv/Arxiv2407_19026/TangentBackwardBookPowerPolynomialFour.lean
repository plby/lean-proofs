import Arxiv.Arxiv2407_19026.TangentBackwardBookPowerPolynomial

/-!
# Transparent fourth-order power-polynomial model for backward book estimates

This file is separate from the completed second-order certificates so that
adding the fourth-order bridge does not invalidate their cached objects.
-/

namespace Arxiv2407_19026

noncomputable section

def backwardLogFourNumeratorPower
    (p : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  let x := rationalPowerSub [1] p
  rationalPowerMul (rationalPowerSub x [1])
    (rationalPowerAdd
      (rationalPowerAdd
        (rationalPowerAdd
          (rationalPowerAdd
            (rationalPowerScale 105 (rationalPowerPow x 8))
            (rationalPowerScale (-136) (rationalPowerPow x 7)))
          (rationalPowerAdd
            (rationalPowerScale 5212 (rationalPowerPow x 6))
            (rationalPowerScale 1096 (rationalPowerPow x 5))))
        (rationalPowerAdd
          (rationalPowerScale 14326 (rationalPowerPow x 4))
          (rationalPowerScale 1096 (rationalPowerPow x 3))))
      (rationalPowerAdd
        (rationalPowerAdd
          (rationalPowerScale 5212 (rationalPowerPow x 2))
          (rationalPowerScale (-136) x))
        [105]))

def backwardLogFourDenominatorPower
    (p : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  let x := rationalPowerSub [1] p
  rationalPowerScale 210
    (rationalPowerMul x
      (rationalPowerPow (rationalPowerAdd x [1]) 7))

def backwardLogFourDenominatorRestPower
    (p : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerScale 210
    (rationalPowerPow (rationalPowerSub [2] p) 7)

def backwardBookDenominatorFourPower
    (blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerMul backwardEntropyDenominatorPower
    (rationalPowerMul
      (backwardLogFourDenominatorPower blue)
      (backwardLogFourDenominatorPower backwardMuPower))

def backwardXLogNumeratorFourPower
    (blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerAdd
    (rationalPowerMul
      (backwardLogFourNumeratorPower blue)
      (backwardLogFourDenominatorRestPower backwardMuPower))
    (rationalPowerMul
      (backwardLogFourNumeratorPower backwardMuPower)
      (backwardLogFourDenominatorPower blue))

def backwardBookBracketNumeratorFourPower
    (β₀ : ℚ) (t blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerAdd
    (backwardXLogNumeratorFourPower blue)
    (rationalPowerMul
      (backwardBookBracketPower β₀ t)
      (rationalPowerMul
        (backwardLogFourDenominatorPower blue)
        (backwardLogFourDenominatorPower backwardMuPower)))

def backwardBookNumeratorFourPower
    (β₀ β₁ : ℚ) (t blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  let blueDen := backwardLogFourDenominatorPower blue
  let muDen :=
    backwardLogFourDenominatorPower backwardMuPower
  rationalPowerAdd
    (rationalPowerMul
      (backwardEntropyRamseyNumeratorPower β₁)
      (rationalPowerMul blueDen muDen))
    (rationalPowerScale (1 / 2)
      (rationalPowerMul
        (backwardBookBracketNumeratorFourPower β₀ t blue)
        backwardEntropyDenominatorPower))

def backwardXLogLowerFourClosed (B z : ℝ) : ℝ :=
  let M := backwardMuUpperNine z
  backwardLogLowerFourClosed (1 - B) * (1 - M)⁻¹ +
    backwardLogLowerFourClosed (1 - M)

def backwardBookLowerFourClosed
    (β₀ β₁ t B z : ℝ) : ℝ :=
  (1 + z) * backwardLogLowerAboveFive (1 + z) +
    (-(1 / 4) * z + β₁ * z ^ 2 + 2 / 25 * z ^ 3) *
      (KernelBounds.expNegTaylor9 z +
        KernelBounds.expNegError10 z) +
    (backwardXLogLowerFourClosed B z - z ^ 2 +
      z * (backwardALogLower β₀ t -
        backwardLogUpperBelowSeven z)) / 2

lemma backwardBookLower_eq_four_closed
    (β₀ β₁ t B z : ℝ)
    (hB1 : B < 1)
    (hM1 : backwardMuUpperNine z < 1) :
    backwardBookLower β₀ β₁ t B z =
      backwardBookLowerFourClosed β₀ β₁ t B z := by
  have hBsub0 : 1 - B ≠ 0 := by linarith
  have hBsub1 : 1 - B + 1 ≠ 0 := by linarith
  have hMsub0 : 1 - backwardMuUpperNine z ≠ 0 := by
    linarith
  have hMsub1 :
      1 - backwardMuUpperNine z + 1 ≠ 0 := by
    linarith
  dsimp [backwardBookLower, backwardXLogLowerFour,
    backwardBookLowerFourClosed, backwardXLogLowerFourClosed]
  rw [backward_log_lower_below_four_closed hBsub0 hBsub1,
    backward_log_lower_below_four_closed hMsub0 hMsub1]

lemma backwardLogFourNumeratorPower_eval
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardLogFourNumeratorPower p) z =
      let x := 1 - rationalPowerEval p z
      (x - 1) *
        (105 * x ^ 8 - 136 * x ^ 7 + 5212 * x ^ 6 +
          1096 * x ^ 5 + 14326 * x ^ 4 + 1096 * x ^ 3 +
          5212 * x ^ 2 - 136 * x + 105) := by
  simp only [backwardLogFourNumeratorPower,
    rationalPowerEval_mul, rationalPowerEval_add,
    rationalPowerEval_sub, rationalPowerEval_scale,
    rationalPowerEval_pow, rationalPowerEval]
  norm_num
  ring_nf
  all_goals simp

lemma backwardLogFourDenominatorPower_eval
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardLogFourDenominatorPower p) z =
      210 * (1 - rationalPowerEval p z) *
        (2 - rationalPowerEval p z) ^ 7 := by
  simp only [backwardLogFourDenominatorPower,
    rationalPowerEval_scale, rationalPowerEval_mul,
    rationalPowerEval_pow, rationalPowerEval_add,
    rationalPowerEval_sub, rationalPowerEval]
  norm_num
  ring

lemma backwardLogFourDenominatorRestPower_eval
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval
        (backwardLogFourDenominatorRestPower p) z =
      210 * (2 - rationalPowerEval p z) ^ 7 := by
  simp only [backwardLogFourDenominatorRestPower,
    rationalPowerEval_scale, rationalPowerEval_pow,
    rationalPowerEval_sub, rationalPowerEval]
  norm_num

lemma backwardLogFourPower_ratio
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardLogFourNumeratorPower p) z /
        rationalPowerEval (backwardLogFourDenominatorPower p) z =
      backwardLogLowerFourClosed
        (1 - rationalPowerEval p z) := by
  rw [backwardLogFourNumeratorPower_eval,
    backwardLogFourDenominatorPower_eval]
  dsimp [backwardLogLowerFourClosed]
  congr 1
  all_goals ring

lemma backwardXLogNumeratorFourPower_ratio
    (blue : RationalPowerPolynomial) (z : ℝ)
    (hblue1 : 1 - rationalPowerEval blue z ≠ 0)
    (hblue2 : 2 - rationalPowerEval blue z ≠ 0)
    (hmu1 : 1 - backwardMuUpperNine z ≠ 0)
    (hmu2 : 2 - backwardMuUpperNine z ≠ 0) :
    rationalPowerEval (backwardXLogNumeratorFourPower blue) z /
        (rationalPowerEval
            (backwardLogFourDenominatorPower blue) z *
          rationalPowerEval
            (backwardLogFourDenominatorPower backwardMuPower) z) =
      backwardXLogLowerFourClosed
        (rationalPowerEval blue z) z := by
  have hblueDen :
      rationalPowerEval
          (backwardLogFourDenominatorPower blue) z ≠ 0 := by
    rw [backwardLogFourDenominatorPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hblue1)
      (pow_ne_zero 7 hblue2)
  have hmuDen :
      rationalPowerEval
          (backwardLogFourDenominatorPower backwardMuPower) z ≠ 0 := by
    rw [backwardLogFourDenominatorPower_eval,
      backwardMuPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hmu1)
      (pow_ne_zero 7 hmu2)
  have hmuRest :
      rationalPowerEval
          (backwardLogFourDenominatorRestPower
            backwardMuPower) z ≠ 0 := by
    rw [backwardLogFourDenominatorRestPower_eval,
      backwardMuPower_eval]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 7 hmu2)
  have hmuFactor :
      rationalPowerEval
          (backwardLogFourDenominatorPower backwardMuPower) z =
        rationalPowerEval
            (backwardLogFourDenominatorRestPower
              backwardMuPower) z *
          (1 - backwardMuUpperNine z) := by
    rw [backwardLogFourDenominatorPower_eval,
      backwardLogFourDenominatorRestPower_eval,
      backwardMuPower_eval]
    ring
  simp only [backwardXLogNumeratorFourPower,
    rationalPowerEval_add, rationalPowerEval_mul]
  calc
    _ =
        (rationalPowerEval
            (backwardLogFourNumeratorPower blue) z /
          rationalPowerEval
            (backwardLogFourDenominatorPower blue) z) *
            (1 - backwardMuUpperNine z)⁻¹ +
          rationalPowerEval
              (backwardLogFourNumeratorPower backwardMuPower) z /
            rationalPowerEval
              (backwardLogFourDenominatorPower
                backwardMuPower) z := by
      rw [hmuFactor]
      field_simp [hblueDen, hmuDen, hmuRest, hmu1]
    _ = _ := by
      rw [backwardLogFourPower_ratio blue z,
        backwardLogFourPower_ratio backwardMuPower z,
        backwardMuPower_eval]
      rfl

lemma backwardBookBracketNumeratorFourPower_ratio
    (β : ℚ) (t blue : RationalPowerPolynomial) (z : ℝ)
    (hblue1 : 1 - rationalPowerEval blue z ≠ 0)
    (hblue2 : 2 - rationalPowerEval blue z ≠ 0)
    (hmu1 : 1 - backwardMuUpperNine z ≠ 0)
    (hmu2 : 2 - backwardMuUpperNine z ≠ 0) :
    rationalPowerEval
          (backwardBookBracketNumeratorFourPower β t blue) z /
        (rationalPowerEval
            (backwardLogFourDenominatorPower blue) z *
          rationalPowerEval
            (backwardLogFourDenominatorPower backwardMuPower) z) =
      backwardXLogLowerFourClosed
          (rationalPowerEval blue z) z -
        z ^ 2 +
        z * (backwardALogLower β
          (rationalPowerEval t z) -
            backwardLogUpperBelowSeven z) := by
  have hblueDen :
      rationalPowerEval
          (backwardLogFourDenominatorPower blue) z ≠ 0 := by
    rw [backwardLogFourDenominatorPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hblue1)
      (pow_ne_zero 7 hblue2)
  have hmuDen :
      rationalPowerEval
          (backwardLogFourDenominatorPower backwardMuPower) z ≠ 0 := by
    rw [backwardLogFourDenominatorPower_eval,
      backwardMuPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hmu1)
      (pow_ne_zero 7 hmu2)
  simp only [backwardBookBracketNumeratorFourPower,
    rationalPowerEval_add, rationalPowerEval_mul]
  calc
    _ =
        rationalPowerEval
              (backwardXLogNumeratorFourPower blue) z /
            (rationalPowerEval
                (backwardLogFourDenominatorPower blue) z *
              rationalPowerEval
                (backwardLogFourDenominatorPower
                  backwardMuPower) z) +
          rationalPowerEval (backwardBookBracketPower β t) z := by
      field_simp [hblueDen, hmuDen]
    _ = _ := by
      rw [backwardXLogNumeratorFourPower_ratio blue z
          hblue1 hblue2 hmu1 hmu2,
        backwardBookBracketPower_eval]
      ring

lemma backwardBookNumeratorFourPower_eval_closed
    (β₀ β₁ : ℚ) (t blue : RationalPowerPolynomial)
    (z : ℝ)
    (hz2 : z + 2 ≠ 0)
    (hblue1 : 1 - rationalPowerEval blue z ≠ 0)
    (hblue2 : 2 - rationalPowerEval blue z ≠ 0)
    (hmu1 : 1 - backwardMuUpperNine z ≠ 0)
    (hmu2 : 2 - backwardMuUpperNine z ≠ 0) :
    rationalPowerEval
          (backwardBookNumeratorFourPower β₀ β₁ t blue) z /
        rationalPowerEval
          (backwardBookDenominatorFourPower blue) z =
      backwardBookLowerFourClosed β₀ β₁
        (rationalPowerEval t z)
        (rationalPowerEval blue z) z := by
  have hentropyDen :
      rationalPowerEval backwardEntropyDenominatorPower z ≠ 0 := by
    rw [backwardEntropyDenominatorPower_eval]
    exact pow_ne_zero 9 hz2
  have hblueDen :
      rationalPowerEval
          (backwardLogFourDenominatorPower blue) z ≠ 0 := by
    rw [backwardLogFourDenominatorPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hblue1)
      (pow_ne_zero 7 hblue2)
  have hmuDen :
      rationalPowerEval
          (backwardLogFourDenominatorPower backwardMuPower) z ≠ 0 := by
    rw [backwardLogFourDenominatorPower_eval,
      backwardMuPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hmu1)
      (pow_ne_zero 7 hmu2)
  simp only [backwardBookNumeratorFourPower,
    backwardBookDenominatorFourPower,
    rationalPowerEval_add, rationalPowerEval_scale,
    rationalPowerEval_mul]
  calc
    _ =
        rationalPowerEval
              (backwardEntropyRamseyNumeratorPower β₁) z /
            rationalPowerEval backwardEntropyDenominatorPower z +
          (rationalPowerEval
              (backwardBookBracketNumeratorFourPower β₀ t blue) z /
            (rationalPowerEval
                (backwardLogFourDenominatorPower blue) z *
              rationalPowerEval
                (backwardLogFourDenominatorPower
                  backwardMuPower) z)) / 2 := by
      field_simp [hentropyDen, hblueDen, hmuDen]
      ring
    _ = _ := by
      rw [backwardEntropyRamseyNumeratorPower_ratio β₁ z hz2,
        backwardBookBracketNumeratorFourPower_ratio β₀ t blue z
          hblue1 hblue2 hmu1 hmu2]
      dsimp [backwardBookLowerFourClosed]

end

end Arxiv2407_19026
