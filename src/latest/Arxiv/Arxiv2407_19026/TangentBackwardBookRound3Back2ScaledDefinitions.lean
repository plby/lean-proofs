import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateData
import Arxiv.Arxiv2407_19026.IntegerPowerPolynomial

/-!
# Scaled-integer model for the round-3 second backward book interval

One common denominator is carried with each power polynomial.  This avoids
normalizing thousands of large rational intermediate coefficients.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

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
    [2023501276929206, -6692654877605140,
      9639054411404975, -6512142340725250,
      1706870482960000]

def scaledBookBlue : ScaledPower :=
  scaledRats 1000000000000
    [44580289499, 952487157437, -942095803365,
      531966378584, -120687127935]

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

def scaledLogFourNumerator (p : ScaledPower) : ScaledPower :=
  let x := scaledSub (scaledInts [1]) p
  scaledMul (scaledSub x (scaledInts [1]))
    (scaledAdd
      (scaledAdd
        (scaledAdd
          (scaledAdd
            (scaledScaleBy 105 1 (scaledPow x 8))
            (scaledScaleBy (-136) 1 (scaledPow x 7)))
          (scaledAdd
            (scaledScaleBy 5212 1 (scaledPow x 6))
            (scaledScaleBy 1096 1 (scaledPow x 5))))
        (scaledAdd
          (scaledScaleBy 14326 1 (scaledPow x 4))
          (scaledScaleBy 1096 1 (scaledPow x 3))))
      (scaledAdd
        (scaledAdd
          (scaledScaleBy 5212 1 (scaledPow x 2))
          (scaledScaleBy (-136) 1 x))
        (scaledInts [105])))

def scaledLogFourDenominator (p : ScaledPower) : ScaledPower :=
  let x := scaledSub (scaledInts [1]) p
  scaledScaleBy 210 1
    (scaledMul x (scaledPow (scaledAdd x (scaledInts [1])) 7))

def scaledLogFourDenominatorRest (p : ScaledPower) : ScaledPower :=
  scaledScaleBy 210 1 (scaledPow (scaledSub (scaledInts [2]) p) 7)

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
        (scaledAdd (scaledConstant 283 1000)
          (scaledScaleBy 127 1000 t))
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
    (scaledMul (scaledLogFourNumerator scaledBookBlue)
      (scaledLogFourDenominatorRest scaledMu))
    (scaledMul (scaledLogFourNumerator scaledMu)
      (scaledLogFourDenominator scaledBookBlue))

def scaledDenProduct : ScaledPower :=
  scaledMul (scaledLogFourDenominator scaledBookBlue)
    (scaledLogFourDenominator scaledMu)

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
  scaledMul (scaledRats 100 [0, -25, 3, 8])
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

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
