import Arxiv.Arxiv2407_19026.TangentBackwardBookBounds

/-!
# Polynomial model for the backward book estimates

The definitions in this file retain the factorization of the analytic
lower bounds.  This lets exact certificates connect to those bounds
without asking `ring` to expand the entire degree-110 expression over
the reals in one step.
-/

namespace Arxiv2407_19026

noncomputable section

abbrev RationalPolynomial := Polynomial ℚ

def rationalPolynomialEval
    (p : RationalPolynomial) (x : ℝ) : ℝ :=
  Polynomial.eval₂ (Rat.castHom ℝ) x p

def rationalPolynomialConstant (q : ℚ) : RationalPolynomial :=
  Polynomial.C q

def backwardTaylorNinePolynomial : RationalPolynomial :=
  1 - Polynomial.X +
    rationalPolynomialConstant (1 / 2) * Polynomial.X ^ 2 -
    rationalPolynomialConstant (1 / 6) * Polynomial.X ^ 3 +
    rationalPolynomialConstant (1 / 24) * Polynomial.X ^ 4 -
    rationalPolynomialConstant (1 / 120) * Polynomial.X ^ 5 +
    rationalPolynomialConstant (1 / 720) * Polynomial.X ^ 6 -
    rationalPolynomialConstant (1 / 5040) * Polynomial.X ^ 7 +
    rationalPolynomialConstant (1 / 40320) * Polynomial.X ^ 8 -
    rationalPolynomialConstant (1 / 362880) * Polynomial.X ^ 9

def backwardErrorTenPolynomial : RationalPolynomial :=
  rationalPolynomialConstant (11 / 36288000) *
    Polynomial.X ^ 10

def backwardMuPolynomial : RationalPolynomial :=
  Polynomial.X *
    (backwardTaylorNinePolynomial +
      backwardErrorTenPolynomial)

def backwardLogTwoNumerator
    (p : RationalPolynomial) : RationalPolynomial :=
  -p * (3 * p ^ 4 - 16 * p ^ 3 + 64 * p ^ 2 -
    96 * p + 48)

def backwardLogTwoDenominator
    (p : RationalPolynomial) : RationalPolynomial :=
  6 * (2 - p) ^ 3 * (1 - p)

def backwardEntropyNumerator : RationalPolynomial :=
  let z : RationalPolynomial := Polynomial.X
  let zPlusTwo := z + 2
  (1 + z) * 2 *
    (z * zPlusTwo ^ 8 +
      rationalPolynomialConstant (1 / 3) *
        z ^ 3 * zPlusTwo ^ 6 +
      rationalPolynomialConstant (1 / 5) *
        z ^ 5 * zPlusTwo ^ 4 +
      rationalPolynomialConstant (1 / 7) *
        z ^ 7 * zPlusTwo ^ 2 +
      rationalPolynomialConstant (1 / 9) * z ^ 9)

def backwardEntropyDenominator : RationalPolynomial :=
  (Polynomial.X + 2) ^ 9

def backwardExpLowerFivePolynomial
    (p : RationalPolynomial) : RationalPolynomial :=
  1 - p + rationalPolynomialConstant (1 / 2) * p ^ 2 -
    rationalPolynomialConstant (1 / 6) * p ^ 3 +
    rationalPolynomialConstant (1 / 24) * p ^ 4 -
    rationalPolynomialConstant (1 / 120) * p ^ 5 -
    rationalPolynomialConstant (7 / 4320) * p ^ 6

def backwardCoordLogUpperPolynomial
    (p : RationalPolynomial) : RationalPolynomial :=
  let s := rationalPolynomialConstant (1 / 2) * (2 - p)
  rationalPolynomialConstant (693147181 / 1000000000) -
    (s + rationalPolynomialConstant (1 / 2) * s ^ 2 +
      rationalPolynomialConstant (1 / 3) * s ^ 3 +
      rationalPolynomialConstant (1 / 4) * s ^ 4 +
      rationalPolynomialConstant (1 / 5) * s ^ 5 +
      rationalPolynomialConstant (1 / 6) * s ^ 6)

def backwardLogUpperSevenPolynomial : RationalPolynomial :=
  let y : RationalPolynomial := 1 - Polynomial.X
  0 - (y + rationalPolynomialConstant (1 / 2) * y ^ 2 +
    rationalPolynomialConstant (1 / 3) * y ^ 3 +
    rationalPolynomialConstant (1 / 4) * y ^ 4 +
    rationalPolynomialConstant (1 / 5) * y ^ 5 +
    rationalPolynomialConstant (1 / 6) * y ^ 6 +
    rationalPolynomialConstant (1 / 7) * y ^ 7)

def backwardALogPolynomial
    (β : ℚ) (t : RationalPolynomial) :
    RationalPolynomial :=
  let βp := rationalPolynomialConstant β
  let coefficient :=
    t ^ 2 * (rationalPolynomialConstant (1 / 4) + βp +
      (rationalPolynomialConstant (4 / 25) - βp) * t -
      rationalPolynomialConstant (2 / 25) * t ^ 2)
  0 - backwardCoordLogUpperPolynomial (1 + t) +
    coefficient * backwardExpLowerFivePolynomial t

def backwardRamseyPolynomial (β : ℚ) :
    RationalPolynomial :=
  let z : RationalPolynomial := Polynomial.X
  (-rationalPolynomialConstant (1 / 4) * z +
      rationalPolynomialConstant β * z ^ 2 +
      rationalPolynomialConstant (2 / 25) * z ^ 3) *
    (backwardTaylorNinePolynomial +
      backwardErrorTenPolynomial)

def backwardBookDenominatorTwo
    (blue : RationalPolynomial) : RationalPolynomial :=
  backwardEntropyDenominator *
    backwardLogTwoDenominator blue *
    backwardLogTwoDenominator backwardMuPolynomial

def backwardBookNumeratorTwo
    (β₀ β₁ : ℚ) (t blue : RationalPolynomial) :
    RationalPolynomial :=
  let z : RationalPolynomial := Polynomial.X
  let mu := backwardMuPolynomial
  let blueDen := backwardLogTwoDenominator blue
  let muDen := backwardLogTwoDenominator mu
  let xLogNumerator :=
    backwardLogTwoNumerator blue *
        (6 * (2 - mu) ^ 3) +
      backwardLogTwoNumerator mu * blueDen
  let bracketNumerator :=
    xLogNumerator +
      (-z ^ 2 +
        z * (backwardALogPolynomial β₀ t -
          backwardLogUpperSevenPolynomial)) *
        blueDen * muDen
  (backwardEntropyNumerator +
      backwardRamseyPolynomial β₁ *
        backwardEntropyDenominator) *
      blueDen * muDen +
    rationalPolynomialConstant (1 / 2) *
      bracketNumerator * backwardEntropyDenominator

def polynomialOfIntegerCoefficients :
    List ℤ → RationalPolynomial
  | [] => 0
  | coefficient :: coefficients =>
      Polynomial.C (coefficient : ℚ) +
        Polynomial.X *
          polynomialOfIntegerCoefficients coefficients

lemma rationalPolynomialEval_ofIntegerCoefficients
    (coefficients : List ℤ) (x : ℝ) :
    rationalPolynomialEval
        (polynomialOfIntegerCoefficients coefficients) x =
      evalIntegerPower coefficients x := by
  induction coefficients with
  | nil =>
      simp [polynomialOfIntegerCoefficients,
        rationalPolynomialEval, evalIntegerPower]
  | cons coefficient coefficients ih =>
      simp only [polynomialOfIntegerCoefficients,
        rationalPolynomialEval, evalIntegerPower,
        Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X]
      change
        Polynomial.eval₂ (Rat.castHom ℝ) x
            (polynomialOfIntegerCoefficients coefficients) =
          evalIntegerPower coefficients x at ih
      rw [ih]
      norm_num

end

end Arxiv2407_19026
