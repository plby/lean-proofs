import Arxiv.Arxiv2407_19026.TangentBackwardBookBounds
import Util.RationalPowerPolynomial

/-!
# Transparent power-polynomial model for backward book estimates

Power polynomials are represented by coefficient lists in ascending
degree order.  Unlike `Polynomial`, this representation has transparent
equality, so the kernel can check generated coefficient identities by
ordinary reduction rather than by a large `ring` normalization.
-/

namespace Arxiv2407_19026

noncomputable section

def backwardTaylorNinePower : RationalPowerPolynomial :=
  [1, -1, 1 / 2, -1 / 6, 1 / 24, -1 / 120,
    1 / 720, -1 / 5040, 1 / 40320, -1 / 362880]

def backwardErrorTenPower : RationalPowerPolynomial :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11 / 36288000]

def backwardMuPower : RationalPowerPolynomial :=
  rationalPowerMul [0, 1]
    (rationalPowerAdd backwardTaylorNinePower
      backwardErrorTenPower)

def backwardLogTwoNumeratorPower
    (p : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerNeg
    (rationalPowerMul p
      (rationalPowerAdd
        (rationalPowerSub
          (rationalPowerAdd
            (rationalPowerScale 3
              (rationalPowerPow p 4))
            (rationalPowerScale 64
              (rationalPowerPow p 2)))
          (rationalPowerScale 16
            (rationalPowerPow p 3)))
        (rationalPowerSub [48]
          (rationalPowerScale 96 p))))

def backwardLogTwoDenominatorPower
    (p : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerScale 6
    (rationalPowerMul
      (rationalPowerPow (rationalPowerSub [2] p) 3)
      (rationalPowerSub [1] p))

def backwardEntropyNumeratorPower :
    RationalPowerPolynomial :=
  let z := [0, 1]
  let zPlusTwo := [2, 1]
  rationalPowerScale 2
    (rationalPowerMul [1, 1]
      (rationalPowerAdd
        (rationalPowerAdd
          (rationalPowerAdd
            (rationalPowerMul z
              (rationalPowerPow zPlusTwo 8))
            (rationalPowerScale (1 / 3)
              (rationalPowerMul
                (rationalPowerPow z 3)
                (rationalPowerPow zPlusTwo 6))))
          (rationalPowerScale (1 / 5)
            (rationalPowerMul
              (rationalPowerPow z 5)
              (rationalPowerPow zPlusTwo 4))))
        (rationalPowerAdd
          (rationalPowerScale (1 / 7)
            (rationalPowerMul
              (rationalPowerPow z 7)
              (rationalPowerPow zPlusTwo 2)))
          (rationalPowerScale (1 / 9)
            (rationalPowerPow z 9)))))

def backwardEntropyDenominatorPower :
    RationalPowerPolynomial :=
  rationalPowerPow [2, 1] 9

def backwardExpLowerFivePower
    (p : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerComp
    [1, -1, 1 / 2, -1 / 6, 1 / 24, -1 / 120,
      -7 / 4320] p

def backwardCoordLogUpperPower
    (p : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  let s :=
    rationalPowerScale (1 / 2)
      (rationalPowerSub [2] p)
  rationalPowerSub [693147181 / 1000000000]
    (rationalPowerComp
      [0, 1, 1 / 2, 1 / 3, 1 / 4, 1 / 5, 1 / 6]
      s)

def backwardLogUpperSevenPower :
    RationalPowerPolynomial :=
  rationalPowerNeg
    (rationalPowerComp
      [0, 1, 1 / 2, 1 / 3, 1 / 4, 1 / 5, 1 / 6,
        1 / 7]
      [1, -1])

def backwardALogPower
    (β : ℚ) (t : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  let coefficient :=
    rationalPowerMul (rationalPowerPow t 2)
      (rationalPowerAdd
        (rationalPowerAdd [1 / 4 + β]
          (rationalPowerScale (4 / 25 - β) t))
        (rationalPowerScale (-2 / 25)
          (rationalPowerPow t 2)))
  rationalPowerAdd
    (rationalPowerNeg
      (backwardCoordLogUpperPower
        (rationalPowerAdd [1] t)))
    (rationalPowerMul coefficient
      (backwardExpLowerFivePower t))

def backwardRamseyPower (β : ℚ) :
    RationalPowerPolynomial :=
  rationalPowerMul
    [0, -1 / 4, β, 2 / 25]
    (rationalPowerAdd backwardTaylorNinePower
      backwardErrorTenPower)

def backwardBookDenominatorTwoPower
    (blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerMul backwardEntropyDenominatorPower
    (rationalPowerMul
      (backwardLogTwoDenominatorPower blue)
      (backwardLogTwoDenominatorPower backwardMuPower))

def backwardXLogNumeratorTwoPower
    (blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerAdd
    (rationalPowerMul
      (backwardLogTwoNumeratorPower blue)
      (rationalPowerScale 6
        (rationalPowerPow
          (rationalPowerSub [2] backwardMuPower) 3)))
    (rationalPowerMul
      (backwardLogTwoNumeratorPower backwardMuPower)
      (backwardLogTwoDenominatorPower blue))

def backwardBookBracketPower
    (β₀ : ℚ) (t : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerAdd
    (rationalPowerNeg (rationalPowerPow [0, 1] 2))
    (rationalPowerMul [0, 1]
      (rationalPowerSub
        (backwardALogPower β₀ t)
        backwardLogUpperSevenPower))

def backwardBookBracketNumeratorTwoPower
    (β₀ : ℚ) (t blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerAdd
    (backwardXLogNumeratorTwoPower blue)
    (rationalPowerMul
      (backwardBookBracketPower β₀ t)
      (rationalPowerMul
        (backwardLogTwoDenominatorPower blue)
        (backwardLogTwoDenominatorPower
          backwardMuPower)))

def backwardEntropyRamseyNumeratorPower
    (β₁ : ℚ) : RationalPowerPolynomial :=
  rationalPowerAdd backwardEntropyNumeratorPower
    (rationalPowerMul (backwardRamseyPower β₁)
      backwardEntropyDenominatorPower)

def backwardBookNumeratorTwoPower
    (β₀ β₁ : ℚ) (t blue : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  let blueDen := backwardLogTwoDenominatorPower blue
  let muDen :=
    backwardLogTwoDenominatorPower backwardMuPower
  rationalPowerAdd
    (rationalPowerMul
      (backwardEntropyRamseyNumeratorPower β₁)
      (rationalPowerMul blueDen muDen))
    (rationalPowerScale (1 / 2)
      (rationalPowerMul
        (backwardBookBracketNumeratorTwoPower β₀ t blue)
        backwardEntropyDenominatorPower))

lemma backwardTaylorNinePower_eval (z : ℝ) :
    rationalPowerEval backwardTaylorNinePower z =
      KernelBounds.expNegTaylor9 z := by
  norm_num [backwardTaylorNinePower, rationalPowerEval,
    KernelBounds.expNegTaylor9, Finset.sum_range_succ,
    Nat.factorial]
  ring

lemma backwardErrorTenPower_eval (z : ℝ) :
    rationalPowerEval backwardErrorTenPower z =
      KernelBounds.expNegError10 z := by
  norm_num [backwardErrorTenPower, rationalPowerEval,
    KernelBounds.expNegError10, Nat.factorial]
  ring

lemma backwardMuPower_eval (z : ℝ) :
    rationalPowerEval backwardMuPower z =
      backwardMuUpperNine z := by
  rw [backwardMuPower, rationalPowerEval_mul,
    rationalPowerEval_add, backwardTaylorNinePower_eval,
    backwardErrorTenPower_eval]
  norm_num [rationalPowerEval, backwardMuUpperNine]

lemma backwardLogTwoNumeratorPower_eval
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardLogTwoNumeratorPower p) z =
      -rationalPowerEval p z *
        (3 * rationalPowerEval p z ^ 4 -
          16 * rationalPowerEval p z ^ 3 +
          64 * rationalPowerEval p z ^ 2 -
          96 * rationalPowerEval p z + 48) := by
  simp only [backwardLogTwoNumeratorPower,
    rationalPowerEval_neg, rationalPowerEval_mul,
    rationalPowerEval_add, rationalPowerEval_sub,
    rationalPowerEval_scale, rationalPowerEval_pow,
    rationalPowerEval]
  norm_num
  ring_nf
  all_goals simp

lemma backwardLogTwoDenominatorPower_eval
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardLogTwoDenominatorPower p) z =
      6 * (2 - rationalPowerEval p z) ^ 3 *
        (1 - rationalPowerEval p z) := by
  simp only [backwardLogTwoDenominatorPower,
    rationalPowerEval_scale, rationalPowerEval_mul,
    rationalPowerEval_pow, rationalPowerEval_sub,
    rationalPowerEval]
  norm_num
  ring

lemma backwardEntropyNumeratorPower_eval (z : ℝ) :
    rationalPowerEval backwardEntropyNumeratorPower z =
      2 * (1 + z) *
        (z * (z + 2) ^ 8 +
          z ^ 3 * (z + 2) ^ 6 / 3 +
          z ^ 5 * (z + 2) ^ 4 / 5 +
          z ^ 7 * (z + 2) ^ 2 / 7 +
          z ^ 9 / 9) := by
  simp only [backwardEntropyNumeratorPower,
    rationalPowerEval_scale, rationalPowerEval_mul,
    rationalPowerEval_add, rationalPowerEval_pow,
    rationalPowerEval]
  norm_num
  ring

lemma backwardEntropyDenominatorPower_eval (z : ℝ) :
    rationalPowerEval backwardEntropyDenominatorPower z =
      (z + 2) ^ 9 := by
  simp [backwardEntropyDenominatorPower,
    rationalPowerEval_pow, rationalPowerEval]
  ring

lemma backwardExpLowerFivePower_eval
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardExpLowerFivePower p) z =
      backwardExpLower5 (rationalPowerEval p z) := by
  rw [backwardExpLowerFivePower, rationalPowerEval_comp]
  norm_num [rationalPowerEval, backwardExpLower5,
    backwardExpTaylor5, backwardExpError6,
    Finset.sum_range_succ, Nat.factorial]
  ring

lemma backwardCoordLogUpperPower_eval
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardCoordLogUpperPower p) z =
      tangentCoordLogUpper (rationalPowerEval p z) := by
  simp only [backwardCoordLogUpperPower,
    rationalPowerEval_sub, rationalPowerEval_comp,
    rationalPowerEval_scale, rationalPowerEval]
  norm_num [tangentCoordLogUpper]
  ring

lemma backwardLogUpperSevenPower_eval (z : ℝ) :
    rationalPowerEval backwardLogUpperSevenPower z =
      backwardLogUpperBelowSeven z := by
  rw [backwardLogUpperSevenPower, rationalPowerEval_neg,
    rationalPowerEval_comp]
  norm_num [rationalPowerEval,
    backwardLogUpperBelowSeven]
  ring

lemma backwardALogPower_eval
    (β : ℚ) (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardALogPower β p) z =
      backwardALogLower β (rationalPowerEval p z) := by
  simp only [backwardALogPower,
    rationalPowerEval_add, rationalPowerEval_neg,
    backwardCoordLogUpperPower_eval,
    rationalPowerEval_mul, rationalPowerEval_pow,
    rationalPowerEval_scale,
    backwardExpLowerFivePower_eval, rationalPowerEval]
  norm_num [backwardALogLower]
  ring_nf
  all_goals simp

lemma backwardRamseyPower_eval
    (β : ℚ) (z : ℝ) :
    rationalPowerEval (backwardRamseyPower β) z =
      (-(1 / 4) * z + β * z ^ 2 + 2 / 25 * z ^ 3) *
        (KernelBounds.expNegTaylor9 z +
          KernelBounds.expNegError10 z) := by
  rw [backwardRamseyPower, rationalPowerEval_mul,
    rationalPowerEval_add, backwardTaylorNinePower_eval,
    backwardErrorTenPower_eval]
  norm_num [rationalPowerEval]
  ring_nf
  all_goals simp

lemma backwardLogTwoPower_ratio
    (p : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardLogTwoNumeratorPower p) z /
        rationalPowerEval (backwardLogTwoDenominatorPower p) z =
      plateauLogLowerBelowOneSub (rationalPowerEval p z) := by
  rw [backwardLogTwoNumeratorPower_eval,
    backwardLogTwoDenominatorPower_eval]
  rfl

lemma backwardEntropyPower_ratio
    (z : ℝ) (hz2 : z + 2 ≠ 0) :
    rationalPowerEval backwardEntropyNumeratorPower z /
        rationalPowerEval backwardEntropyDenominatorPower z =
      (1 + z) * backwardLogLowerAboveFive (1 + z) := by
  rw [backwardEntropyNumeratorPower_eval,
    backwardEntropyDenominatorPower_eval]
  have hratio :
      ((1 + z - 1) / (1 + z + 1) : ℝ) =
        z / (z + 2) := by
    congr 1 <;> ring
  simp only [backwardLogLowerAboveFive, hratio]
  field_simp [hz2]

lemma backwardXLogNumeratorTwoPower_ratio
    (blue : RationalPowerPolynomial) (z : ℝ)
    (hblue1 : 1 - rationalPowerEval blue z ≠ 0)
    (hblue2 : 2 - rationalPowerEval blue z ≠ 0)
    (hmu1 : 1 - backwardMuUpperNine z ≠ 0)
    (hmu2 : 2 - backwardMuUpperNine z ≠ 0) :
    rationalPowerEval (backwardXLogNumeratorTwoPower blue) z /
        (rationalPowerEval
            (backwardLogTwoDenominatorPower blue) z *
          rationalPowerEval
            (backwardLogTwoDenominatorPower backwardMuPower) z) =
      plateauLogLowerBelowOneSub
          (rationalPowerEval blue z) *
        (1 - backwardMuUpperNine z)⁻¹ +
      plateauLogLowerBelowOneSub (backwardMuUpperNine z) := by
  simp only [backwardXLogNumeratorTwoPower,
    rationalPowerEval_add, rationalPowerEval_mul,
    rationalPowerEval_scale, rationalPowerEval_pow,
    rationalPowerEval_sub, rationalPowerEval,
    backwardLogTwoNumeratorPower_eval,
    backwardLogTwoDenominatorPower_eval,
    backwardMuPower_eval]
  dsimp [plateauLogLowerBelowOneSub]
  field_simp [hblue1, hblue2, hmu1, hmu2]
  ring

lemma backwardBookBracketPower_eval
    (β : ℚ) (t : RationalPowerPolynomial) (z : ℝ) :
    rationalPowerEval (backwardBookBracketPower β t) z =
      -z ^ 2 +
        z * (backwardALogLower β
          (rationalPowerEval t z) -
            backwardLogUpperBelowSeven z) := by
  rw [backwardBookBracketPower,
    rationalPowerEval_add, rationalPowerEval_neg,
    rationalPowerEval_pow, rationalPowerEval_mul,
    rationalPowerEval_sub, backwardALogPower_eval,
    backwardLogUpperSevenPower_eval]
  norm_num [rationalPowerEval]

lemma backwardBookBracketNumeratorTwoPower_ratio
    (β : ℚ) (t blue : RationalPowerPolynomial) (z : ℝ)
    (hblue1 : 1 - rationalPowerEval blue z ≠ 0)
    (hblue2 : 2 - rationalPowerEval blue z ≠ 0)
    (hmu1 : 1 - backwardMuUpperNine z ≠ 0)
    (hmu2 : 2 - backwardMuUpperNine z ≠ 0) :
    rationalPowerEval
          (backwardBookBracketNumeratorTwoPower β t blue) z /
        (rationalPowerEval
            (backwardLogTwoDenominatorPower blue) z *
          rationalPowerEval
            (backwardLogTwoDenominatorPower backwardMuPower) z) =
      plateauLogLowerBelowOneSub
          (rationalPowerEval blue z) *
        (1 - backwardMuUpperNine z)⁻¹ +
      plateauLogLowerBelowOneSub (backwardMuUpperNine z) -
      z ^ 2 +
      z * (backwardALogLower β
        (rationalPowerEval t z) -
          backwardLogUpperBelowSeven z) := by
  have hblueDen :
      rationalPowerEval
          (backwardLogTwoDenominatorPower blue) z ≠ 0 := by
    rw [backwardLogTwoDenominatorPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hblue2))
      hblue1
  have hmuDen :
      rationalPowerEval
          (backwardLogTwoDenominatorPower backwardMuPower) z ≠ 0 := by
    rw [backwardLogTwoDenominatorPower_eval,
      backwardMuPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hmu2))
      hmu1
  simp only [backwardBookBracketNumeratorTwoPower,
    rationalPowerEval_add, rationalPowerEval_mul]
  calc
    _ =
        rationalPowerEval
              (backwardXLogNumeratorTwoPower blue) z /
            (rationalPowerEval
                (backwardLogTwoDenominatorPower blue) z *
              rationalPowerEval
                (backwardLogTwoDenominatorPower
                  backwardMuPower) z) +
          rationalPowerEval (backwardBookBracketPower β t) z := by
      field_simp [hblueDen, hmuDen]
    _ = _ := by
      rw [backwardXLogNumeratorTwoPower_ratio blue z
          hblue1 hblue2 hmu1 hmu2,
        backwardBookBracketPower_eval]
      ring

lemma backwardEntropyRamseyNumeratorPower_ratio
    (β : ℚ) (z : ℝ) (hz2 : z + 2 ≠ 0) :
    rationalPowerEval
          (backwardEntropyRamseyNumeratorPower β) z /
        rationalPowerEval backwardEntropyDenominatorPower z =
      (1 + z) * backwardLogLowerAboveFive (1 + z) +
        (-(1 / 4) * z + β * z ^ 2 + 2 / 25 * z ^ 3) *
          (KernelBounds.expNegTaylor9 z +
            KernelBounds.expNegError10 z) := by
  have hden :
      rationalPowerEval backwardEntropyDenominatorPower z ≠ 0 := by
    rw [backwardEntropyDenominatorPower_eval]
    exact pow_ne_zero 9 hz2
  rw [backwardEntropyRamseyNumeratorPower,
    rationalPowerEval_add, rationalPowerEval_mul]
  calc
    _ =
        rationalPowerEval backwardEntropyNumeratorPower z /
            rationalPowerEval backwardEntropyDenominatorPower z +
          rationalPowerEval (backwardRamseyPower β) z := by
      field_simp [hden]
    _ = _ := by
      rw [backwardEntropyPower_ratio z hz2,
        backwardRamseyPower_eval]

lemma backwardBookNumeratorTwoPower_eval_closed
    (β₀ β₁ : ℚ) (t blue : RationalPowerPolynomial)
    (z : ℝ)
    (hz2 : z + 2 ≠ 0)
    (hblue1 : 1 - rationalPowerEval blue z ≠ 0)
    (hblue2 : 2 - rationalPowerEval blue z ≠ 0)
    (hmu1 : 1 - backwardMuUpperNine z ≠ 0)
    (hmu2 : 2 - backwardMuUpperNine z ≠ 0) :
    rationalPowerEval
          (backwardBookNumeratorTwoPower β₀ β₁ t blue) z /
        rationalPowerEval
          (backwardBookDenominatorTwoPower blue) z =
      backwardBookLowerTwoClosed β₀ β₁
        (rationalPowerEval t z)
        (rationalPowerEval blue z) z := by
  have hentropyDen :
      rationalPowerEval backwardEntropyDenominatorPower z ≠ 0 := by
    rw [backwardEntropyDenominatorPower_eval]
    exact pow_ne_zero 9 hz2
  have hblueDen :
      rationalPowerEval
          (backwardLogTwoDenominatorPower blue) z ≠ 0 := by
    rw [backwardLogTwoDenominatorPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hblue2))
      hblue1
  have hmuDen :
      rationalPowerEval
          (backwardLogTwoDenominatorPower backwardMuPower) z ≠ 0 := by
    rw [backwardLogTwoDenominatorPower_eval,
      backwardMuPower_eval]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hmu2))
      hmu1
  simp only [backwardBookNumeratorTwoPower,
    backwardBookDenominatorTwoPower,
    rationalPowerEval_add, rationalPowerEval_scale,
    rationalPowerEval_mul]
  calc
    _ =
        rationalPowerEval
              (backwardEntropyRamseyNumeratorPower β₁) z /
            rationalPowerEval backwardEntropyDenominatorPower z +
          (rationalPowerEval
              (backwardBookBracketNumeratorTwoPower β₀ t blue) z /
            (rationalPowerEval
                (backwardLogTwoDenominatorPower blue) z *
              rationalPowerEval
                (backwardLogTwoDenominatorPower
                  backwardMuPower) z)) / 2 := by
      field_simp [hentropyDen, hblueDen, hmuDen]
      ring
    _ = _ := by
      rw [backwardEntropyRamseyNumeratorPower_ratio β₁ z hz2,
        backwardBookBracketNumeratorTwoPower_ratio β₀ t blue z
          hblue1 hblue2 hmu1 hmu2]
      dsimp [backwardBookLowerTwoClosed]

end

end Arxiv2407_19026
