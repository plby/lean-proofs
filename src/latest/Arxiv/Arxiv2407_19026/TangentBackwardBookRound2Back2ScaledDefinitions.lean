import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2Certificate
import Arxiv.Arxiv2407_19026.IntegerPowerPolynomial

/-!
# Scaled-integer model for the round-2 second backward book interval

One common denominator is carried with each power polynomial.  This avoids
normalizing thousands of large rational intermediate coefficients.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back2Certificate

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
  scaledRats 625000000000000
    [2066381206269706, -6848604810621590,
      9870087277671600, -6670315592419625,
      1748484874535000]

def scaledBookBlue : ScaledPower :=
  scaledRats 1000000000000
    [44885591902, 949847557630, -939512012139,
      531126231165, -120610755372]

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

def scaledLogThreeNumerator (p : ScaledPower) : ScaledPower :=
  let x := scaledSub (scaledInts [1]) p
  scaledMul (scaledSub x (scaledInts [1]))
    (scaledAdd
      (scaledAdd
        (scaledAdd
          (scaledScaleBy 15 1 (scaledPow x 6))
          (scaledScaleBy 2 1 (scaledPow x 5)))
        (scaledAdd
          (scaledScaleBy 417 1 (scaledPow x 4))
          (scaledScaleBy 92 1 (scaledPow x 3))))
      (scaledAdd
        (scaledScaleBy 417 1 (scaledPow x 2))
        (scaledAdd
          (scaledScaleBy 2 1 x)
          (scaledInts [15]))))

def scaledLogThreeDenominator (p : ScaledPower) : ScaledPower :=
  let x := scaledSub (scaledInts [1]) p
  scaledScaleBy 30 1
    (scaledMul x (scaledPow (scaledAdd x (scaledInts [1])) 5))

def scaledLogThreeDenominatorRest (p : ScaledPower) : ScaledPower :=
  scaledScaleBy 30 1 (scaledPow (scaledSub (scaledInts [2]) p) 5)

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
        (scaledAdd (scaledConstant 59 200)
          (scaledScaleBy 23 200 t))
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
    (scaledMul (scaledLogThreeNumerator scaledBookBlue)
      (scaledLogThreeDenominatorRest scaledMu))
    (scaledMul (scaledLogThreeNumerator scaledMu)
      (scaledLogThreeDenominator scaledBookBlue))

def scaledDenProduct : ScaledPower :=
  scaledMul (scaledLogThreeDenominator scaledBookBlue)
    (scaledLogThreeDenominator scaledMu)

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
  scaledMul (scaledRats 1000 [0, -250, 33, 80])
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

end BackwardBookRound2Back2Certificate
end Arxiv2407_19026
