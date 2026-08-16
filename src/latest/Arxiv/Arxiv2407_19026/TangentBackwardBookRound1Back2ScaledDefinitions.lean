import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2Certificate
import Arxiv.Arxiv2407_19026.IntegerPowerPolynomial

/-!
# Scaled-integer model for the round-1 second backward book interval

One common denominator is carried with each power polynomial.  This avoids
normalizing thousands of large rational intermediate coefficients.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Certificate

noncomputable section

abbrev ScaledPower := ScaledIntegerPower

def scaledInts (coefficients : List ℤ) : ScaledPower :=
  ScaledIntegerPower.ofIntegers 1 coefficients (by norm_num)

def scaledRats (scale : ℕ) (coefficients : List ℤ)
    (hscale : scale ≠ 0 := by norm_num) : ScaledPower :=
  ScaledIntegerPower.ofIntegers scale coefficients hscale

def scaledConstant (numerator : ℤ) (denominator : ℕ)
    (hdenominator : denominator ≠ 0 := by norm_num) : ScaledPower :=
  ScaledIntegerPower.constant numerator denominator hdenominator

def scaledAdd := ScaledIntegerPower.add
def scaledNeg := ScaledIntegerPower.neg
def scaledSub := ScaledIntegerPower.sub
def scaledMul := ScaledIntegerPower.mul
def scaledPow := ScaledIntegerPower.pow
def scaledComp := ScaledIntegerPower.comp

def scaledScaleBy (numerator : ℤ) (denominator : ℕ)
    (p : ScaledPower)
    (hdenominator : denominator ≠ 0 := by norm_num) : ScaledPower :=
  ScaledIntegerPower.scaleBy numerator denominator hdenominator p

def scaledBookT : ScaledPower :=
  scaledRats 25000000000000
    [87920866233937, -292786922765386,
      422398361723155, -285525751865925,
      74821374734750]

def scaledBookBlue : ScaledPower :=
  scaledRats 1000000000000
    [46095949483, 939350932290, -929240184248,
      527782166713, -120303698398]

def scaledTaylorNine : ScaledPower :=
  scaledRats 362880
    [362880, -362880, 181440, -60480, 15120,
      -3024, 504, -72, 9, -1]

def scaledErrorTen : ScaledPower :=
  scaledRats 36288000
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11]

def scaledMu : ScaledPower :=
  scaledMul (scaledInts [0, 1])
    (scaledAdd scaledTaylorNine scaledErrorTen)

def scaledLogTwoNumerator (p : ScaledPower) : ScaledPower :=
  scaledNeg
    (scaledMul p
      (scaledAdd
        (scaledSub
          (scaledAdd
            (scaledScaleBy 3 1 (scaledPow p 4))
            (scaledScaleBy 64 1 (scaledPow p 2)))
          (scaledScaleBy 16 1 (scaledPow p 3)))
        (scaledSub (scaledInts [48])
          (scaledScaleBy 96 1 p))))

def scaledLogTwoDenominator (p : ScaledPower) : ScaledPower :=
  scaledScaleBy 6 1
    (scaledMul (scaledPow (scaledSub (scaledInts [2]) p) 3)
      (scaledSub (scaledInts [1]) p))

def scaledLogTwoDenominatorRest (p : ScaledPower) : ScaledPower :=
  scaledScaleBy 6 1 (scaledPow (scaledSub (scaledInts [2]) p) 3)

def scaledExpLowerFive (p : ScaledPower) : ScaledPower :=
  scaledComp
    (scaledRats 4320 [4320, -4320, 2160, -720, 180, -36, -7]) p

def scaledCoordLogUpper (p : ScaledPower) : ScaledPower :=
  let s := scaledScaleBy 1 2 (scaledSub (scaledInts [2]) p)
  scaledSub (scaledConstant 693147181 1000000000)
    (scaledComp
      (scaledRats 60 [0, 60, 30, 20, 15, 12, 10]) s)

def scaledLogUpperSeven : ScaledPower :=
  scaledNeg
    (scaledComp
      (scaledRats 420 [0, 420, 210, 140, 105, 84, 70, 60])
      (scaledInts [1, -1]))

def scaledALog : ScaledPower :=
  let t := scaledBookT
  let coefficient :=
    scaledMul (scaledPow t 2)
      (scaledAdd
        (scaledAdd (scaledConstant 33 100)
          (scaledScaleBy 2 25 t))
        (scaledScaleBy (-2) 25 (scaledPow t 2)))
  scaledAdd
    (scaledNeg (scaledCoordLogUpper (scaledAdd (scaledInts [1]) t)))
    (scaledMul coefficient (scaledExpLowerFive t))

def scaledBookBracket : ScaledPower :=
  scaledAdd (scaledNeg (scaledPow (scaledInts [0, 1]) 2))
    (scaledMul (scaledInts [0, 1])
      (scaledSub scaledALog scaledLogUpperSeven))

def scaledXLogNumerator : ScaledPower :=
  scaledAdd
    (scaledMul (scaledLogTwoNumerator scaledBookBlue)
      (scaledLogTwoDenominatorRest scaledMu))
    (scaledMul (scaledLogTwoNumerator scaledMu)
      (scaledLogTwoDenominator scaledBookBlue))

def scaledDenProduct : ScaledPower :=
  scaledMul (scaledLogTwoDenominator scaledBookBlue)
    (scaledLogTwoDenominator scaledMu)

def scaledBracketNumerator : ScaledPower :=
  scaledAdd scaledXLogNumerator
    (scaledMul scaledBookBracket scaledDenProduct)

def scaledEntropyNumerator : ScaledPower :=
  let z := scaledInts [0, 1]
  let zPlusTwo := scaledInts [2, 1]
  scaledScaleBy 2 1
    (scaledMul (scaledInts [1, 1])
      (scaledAdd
        (scaledAdd
          (scaledAdd
            (scaledMul z (scaledPow zPlusTwo 8))
            (scaledScaleBy 1 3
              (scaledMul (scaledPow z 3) (scaledPow zPlusTwo 6))))
          (scaledScaleBy 1 5
            (scaledMul (scaledPow z 5) (scaledPow zPlusTwo 4))))
        (scaledAdd
          (scaledScaleBy 1 7
            (scaledMul (scaledPow z 7) (scaledPow zPlusTwo 2)))
          (scaledScaleBy 1 9 (scaledPow z 9)))))

def scaledEntropyDenominator : ScaledPower :=
  scaledPow (scaledInts [2, 1]) 9

def scaledRamsey : ScaledPower :=
  scaledMul (scaledRats 200 [0, -50, 9, 16])
    (scaledAdd scaledTaylorNine scaledErrorTen)

def scaledEntropyRamseyNumerator : ScaledPower :=
  scaledAdd scaledEntropyNumerator
    (scaledMul scaledRamsey scaledEntropyDenominator)

def scaledBookNumerator : ScaledPower :=
  scaledAdd
    (scaledMul scaledEntropyRamseyNumerator scaledDenProduct)
    (scaledScaleBy 1 2
      (scaledMul scaledBracketNumerator scaledEntropyDenominator))

end

end BackwardBookRound1Back2Certificate
end Arxiv2407_19026
