import Arxiv.Arxiv2407_19026.TangentBackwardBookPowerPolynomial

/-!
# Transparent third-order power-polynomial model for backward book estimates

This file is separate from the completed second-order certificates so that
adding the third-order bridge does not invalidate their cached objects.
-/

namespace Arxiv2407_19026

noncomputable section

def backwardLogThreeNumeratorPower
    (p : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  let x := rationalPowerSub [1] p
  rationalPowerMul (rationalPowerSub x [1])
    (rationalPowerAdd
      (rationalPowerAdd
        (rationalPowerAdd
          (rationalPowerScale 15 (rationalPowerPow x 6))
          (rationalPowerScale 2 (rationalPowerPow x 5)))
        (rationalPowerAdd
          (rationalPowerScale 417 (rationalPowerPow x 4))
          (rationalPowerScale 92 (rationalPowerPow x 3))))
      (rationalPowerAdd
        (rationalPowerScale 417 (rationalPowerPow x 2))
        (rationalPowerAdd (rationalPowerScale 2 x) [15])))

def backwardLogThreeDenominatorPower
    (p : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  let x := rationalPowerSub [1] p
  rationalPowerScale 30
    (rationalPowerMul x
      (rationalPowerPow (rationalPowerAdd x [1]) 5))

def backwardLogThreeDenominatorRestPower
    (p : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerScale 30
    (rationalPowerPow (rationalPowerSub [2] p) 5)

def backwardBookDenominatorThreePower
    (blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerMul backwardEntropyDenominatorPower
    (rationalPowerMul
      (backwardLogThreeDenominatorPower blue)
      (backwardLogThreeDenominatorPower backwardMuPower))

def backwardXLogNumeratorThreePower
    (blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerAdd
    (rationalPowerMul
      (backwardLogThreeNumeratorPower blue)
      (backwardLogThreeDenominatorRestPower backwardMuPower))
    (rationalPowerMul
      (backwardLogThreeNumeratorPower backwardMuPower)
      (backwardLogThreeDenominatorPower blue))

def backwardBookBracketNumeratorThreePower
    (β₀ : ℚ) (t blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerAdd
    (backwardXLogNumeratorThreePower blue)
    (rationalPowerMul
      (backwardBookBracketPower β₀ t)
      (rationalPowerMul
        (backwardLogThreeDenominatorPower blue)
        (backwardLogThreeDenominatorPower backwardMuPower)))

def backwardBookNumeratorThreePower
    (β₀ β₁ : ℚ) (t blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  let blueDen := backwardLogThreeDenominatorPower blue
  let muDen :=
    backwardLogThreeDenominatorPower backwardMuPower
  rationalPowerAdd
    (rationalPowerMul
      (backwardEntropyRamseyNumeratorPower β₁)
      (rationalPowerMul blueDen muDen))
    (rationalPowerScale (1 / 2)
      (rationalPowerMul
        (backwardBookBracketNumeratorThreePower β₀ t blue)
        backwardEntropyDenominatorPower))

def backwardXLogLowerThreeClosed (B z : ℝ) : ℝ :=
  let M := backwardMuUpperNine z
  backwardLogLowerThreeClosed (1 - B) * (1 - M)⁻¹ +
    backwardLogLowerThreeClosed (1 - M)

def backwardBookLowerThreeClosed
    (β₀ β₁ t B z : ℝ) : ℝ :=
  (1 + z) * backwardLogLowerAboveFive (1 + z) +
    (-(1 / 4) * z + β₁ * z ^ 2 + 2 / 25 * z ^ 3) *
      (KernelBounds.expNegTaylor9 z +
        KernelBounds.expNegError10 z) +
    (backwardXLogLowerThreeClosed B z - z ^ 2 +
      z * (backwardALogLower β₀ t -
        backwardLogUpperBelowSeven z)) / 2

lemma backwardBookLowerThree_eq_closed
    (β₀ β₁ t B z : ℝ)
    (hB1 : B < 1)
    (hM1 : backwardMuUpperNine z < 1) :
    backwardBookLowerThree β₀ β₁ t B z =
      backwardBookLowerThreeClosed β₀ β₁ t B z := by
  have hBsub0 : 1 - B ≠ 0 := by linarith
  have hBsub1 : 1 - B + 1 ≠ 0 := by linarith
  have hMsub0 : 1 - backwardMuUpperNine z ≠ 0 := by
    linarith
  have hMsub1 :
      1 - backwardMuUpperNine z + 1 ≠ 0 := by
    linarith
  dsimp [backwardBookLowerThree, backwardXLogLowerThree,
    backwardBookLowerThreeClosed, backwardXLogLowerThreeClosed]
  rw [backward_log_lower_below_three_closed hBsub0 hBsub1,
    backward_log_lower_below_three_closed hMsub0 hMsub1]

lemma backwardLogThreeNumeratorPower_eval
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardLogThreeNumeratorPower p) z =
      let x := 1 - rationalPowerEval p z
      (x - 1) *
        (15 * x ^ 6 + 2 * x ^ 5 + 417 * x ^ 4 +
          92 * x ^ 3 + 417 * x ^ 2 + 2 * x + 15) := by
  simp only [backwardLogThreeNumeratorPower,
    rationalPowerEval_mul, rationalPowerEval_add,
    rationalPowerEval_sub, rationalPowerEval_scale,
    rationalPowerEval_pow, rationalPowerEval]
  norm_num
  ring_nf
  all_goals simp

lemma backwardLogThreeDenominatorPower_eval
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardLogThreeDenominatorPower p) z =
      30 * (1 - rationalPowerEval p z) *
        (2 - rationalPowerEval p z) ^ 5 := by
  simp only [backwardLogThreeDenominatorPower,
    rationalPowerEval_scale, rationalPowerEval_mul,
    rationalPowerEval_pow, rationalPowerEval_add,
    rationalPowerEval_sub, rationalPowerEval]
  norm_num
  ring

lemma backwardLogThreeDenominatorRestPower_eval
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval
        (backwardLogThreeDenominatorRestPower p) z =
      30 * (2 - rationalPowerEval p z) ^ 5 := by
  simp only [backwardLogThreeDenominatorRestPower,
    rationalPowerEval_scale, rationalPowerEval_pow,
    rationalPowerEval_sub, rationalPowerEval]
  norm_num

lemma backwardLogThreePower_ratio
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardLogThreeNumeratorPower p) z /
        rationalPowerEval (backwardLogThreeDenominatorPower p) z =
      backwardLogLowerThreeClosed
        (1 - rationalPowerEval p z) := by
  rw [backwardLogThreeNumeratorPower_eval,
    backwardLogThreeDenominatorPower_eval]
  dsimp [backwardLogLowerThreeClosed]
  congr 1
  all_goals ring

lemma backwardXLogNumeratorThreePower_ratio
    (blue : RationalPowerPolynomial) (z : ℝ)
    (hblue1 : 1 - rationalPowerEval blue z ≠ 0)
    (hblue2 : 2 - rationalPowerEval blue z ≠ 0)
    (hmu1 : 1 - backwardMuUpperNine z ≠ 0)
    (hmu2 : 2 - backwardMuUpperNine z ≠ 0) :
    rationalPowerEval (backwardXLogNumeratorThreePower blue) z /
        (rationalPowerEval
            (backwardLogThreeDenominatorPower blue) z *
          rationalPowerEval
            (backwardLogThreeDenominatorPower backwardMuPower) z) =
      backwardXLogLowerThreeClosed
        (rationalPowerEval blue z) z := by
  have hblueDen :
      rationalPowerEval
          (backwardLogThreeDenominatorPower blue) z ≠ 0 := by
    rw [backwardLogThreeDenominatorPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hblue1)
      (pow_ne_zero 5 hblue2)
  have hmuDen :
      rationalPowerEval
          (backwardLogThreeDenominatorPower backwardMuPower) z ≠ 0 := by
    rw [backwardLogThreeDenominatorPower_eval,
      backwardMuPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hmu1)
      (pow_ne_zero 5 hmu2)
  have hmuRest :
      rationalPowerEval
          (backwardLogThreeDenominatorRestPower
            backwardMuPower) z ≠ 0 := by
    rw [backwardLogThreeDenominatorRestPower_eval,
      backwardMuPower_eval]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 5 hmu2)
  have hmuFactor :
      rationalPowerEval
          (backwardLogThreeDenominatorPower backwardMuPower) z =
        rationalPowerEval
            (backwardLogThreeDenominatorRestPower
              backwardMuPower) z *
          (1 - backwardMuUpperNine z) := by
    rw [backwardLogThreeDenominatorPower_eval,
      backwardLogThreeDenominatorRestPower_eval,
      backwardMuPower_eval]
    ring
  simp only [backwardXLogNumeratorThreePower,
    rationalPowerEval_add, rationalPowerEval_mul]
  calc
    _ =
        (rationalPowerEval
            (backwardLogThreeNumeratorPower blue) z /
          rationalPowerEval
            (backwardLogThreeDenominatorPower blue) z) *
            (1 - backwardMuUpperNine z)⁻¹ +
          rationalPowerEval
              (backwardLogThreeNumeratorPower backwardMuPower) z /
            rationalPowerEval
              (backwardLogThreeDenominatorPower
                backwardMuPower) z := by
      rw [hmuFactor]
      field_simp [hblueDen, hmuDen, hmuRest, hmu1]
    _ = _ := by
      rw [backwardLogThreePower_ratio blue z,
        backwardLogThreePower_ratio backwardMuPower z,
        backwardMuPower_eval]
      rfl

lemma backwardBookBracketNumeratorThreePower_ratio
    (β : ℚ) (t blue : RationalPowerPolynomial) (z : ℝ)
    (hblue1 : 1 - rationalPowerEval blue z ≠ 0)
    (hblue2 : 2 - rationalPowerEval blue z ≠ 0)
    (hmu1 : 1 - backwardMuUpperNine z ≠ 0)
    (hmu2 : 2 - backwardMuUpperNine z ≠ 0) :
    rationalPowerEval
          (backwardBookBracketNumeratorThreePower β t blue) z /
        (rationalPowerEval
            (backwardLogThreeDenominatorPower blue) z *
          rationalPowerEval
            (backwardLogThreeDenominatorPower backwardMuPower) z) =
      backwardXLogLowerThreeClosed
          (rationalPowerEval blue z) z -
        z ^ 2 +
        z * (backwardALogLower β
          (rationalPowerEval t z) -
            backwardLogUpperBelowSeven z) := by
  have hblueDen :
      rationalPowerEval
          (backwardLogThreeDenominatorPower blue) z ≠ 0 := by
    rw [backwardLogThreeDenominatorPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hblue1)
      (pow_ne_zero 5 hblue2)
  have hmuDen :
      rationalPowerEval
          (backwardLogThreeDenominatorPower backwardMuPower) z ≠ 0 := by
    rw [backwardLogThreeDenominatorPower_eval,
      backwardMuPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hmu1)
      (pow_ne_zero 5 hmu2)
  simp only [backwardBookBracketNumeratorThreePower,
    rationalPowerEval_add, rationalPowerEval_mul]
  calc
    _ =
        rationalPowerEval
              (backwardXLogNumeratorThreePower blue) z /
            (rationalPowerEval
                (backwardLogThreeDenominatorPower blue) z *
              rationalPowerEval
                (backwardLogThreeDenominatorPower
                  backwardMuPower) z) +
          rationalPowerEval (backwardBookBracketPower β t) z := by
      field_simp [hblueDen, hmuDen]
    _ = _ := by
      rw [backwardXLogNumeratorThreePower_ratio blue z
          hblue1 hblue2 hmu1 hmu2,
        backwardBookBracketPower_eval]
      ring

lemma backwardBookNumeratorThreePower_eval_closed
    (β₀ β₁ : ℚ) (t blue : RationalPowerPolynomial)
    (z : ℝ)
    (hz2 : z + 2 ≠ 0)
    (hblue1 : 1 - rationalPowerEval blue z ≠ 0)
    (hblue2 : 2 - rationalPowerEval blue z ≠ 0)
    (hmu1 : 1 - backwardMuUpperNine z ≠ 0)
    (hmu2 : 2 - backwardMuUpperNine z ≠ 0) :
    rationalPowerEval
          (backwardBookNumeratorThreePower β₀ β₁ t blue) z /
        rationalPowerEval
          (backwardBookDenominatorThreePower blue) z =
      backwardBookLowerThreeClosed β₀ β₁
        (rationalPowerEval t z)
        (rationalPowerEval blue z) z := by
  have hentropyDen :
      rationalPowerEval backwardEntropyDenominatorPower z ≠ 0 := by
    rw [backwardEntropyDenominatorPower_eval]
    exact pow_ne_zero 9 hz2
  have hblueDen :
      rationalPowerEval
          (backwardLogThreeDenominatorPower blue) z ≠ 0 := by
    rw [backwardLogThreeDenominatorPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hblue1)
      (pow_ne_zero 5 hblue2)
  have hmuDen :
      rationalPowerEval
          (backwardLogThreeDenominatorPower backwardMuPower) z ≠ 0 := by
    rw [backwardLogThreeDenominatorPower_eval,
      backwardMuPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) hmu1)
      (pow_ne_zero 5 hmu2)
  simp only [backwardBookNumeratorThreePower,
    backwardBookDenominatorThreePower,
    rationalPowerEval_add, rationalPowerEval_scale,
    rationalPowerEval_mul]
  calc
    _ =
        rationalPowerEval
              (backwardEntropyRamseyNumeratorPower β₁) z /
            rationalPowerEval backwardEntropyDenominatorPower z +
          (rationalPowerEval
              (backwardBookBracketNumeratorThreePower β₀ t blue) z /
            (rationalPowerEval
                (backwardLogThreeDenominatorPower blue) z *
              rationalPowerEval
                (backwardLogThreeDenominatorPower
                  backwardMuPower) z)) / 2 := by
      field_simp [hentropyDen, hblueDen, hmuDen]
      ring
    _ = _ := by
      rw [backwardEntropyRamseyNumeratorPower_ratio β₁ z hz2,
        backwardBookBracketNumeratorThreePower_ratio β₀ t blue z
          hblue1 hblue2 hmu1 hmu2]
      dsimp [backwardBookLowerThreeClosed]

end

end Arxiv2407_19026
