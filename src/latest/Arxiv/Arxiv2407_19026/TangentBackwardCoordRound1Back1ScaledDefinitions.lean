import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back1Certificate
import Arxiv.Arxiv2407_19026.IntegerPowerPolynomial

/-!
# Scaled-integer model for the round-1 first backward coordinate bound

The semantic proof has two large rational identities.  This model carries one
common denominator with each power polynomial, so those identities can be
checked as a sequence of modest integer coefficient calculations.
-/

namespace Arxiv2407_19026
namespace BackwardCoordRound1Back1Certificate

noncomputable section

abbrev CoordScaledPower := ScaledIntegerPower

def coordScaledInts (coefficients : List ℤ) : CoordScaledPower :=
  ScaledIntegerPower.ofIntegers 1 coefficients (by norm_num)

def coordScaledRats (scale : ℕ) (coefficients : List ℤ)
    (hscale : scale ≠ 0 := by norm_num) : CoordScaledPower :=
  ScaledIntegerPower.ofIntegers scale coefficients hscale

def coordScaledConstant (numerator : ℤ) (denominator : ℕ)
    (hdenominator : denominator ≠ 0 := by norm_num) : CoordScaledPower :=
  ScaledIntegerPower.constant numerator denominator hdenominator

def coordScaledAdd := ScaledIntegerPower.add
def coordScaledNeg := ScaledIntegerPower.neg
def coordScaledSub := ScaledIntegerPower.sub
def coordScaledMul := ScaledIntegerPower.mul
def coordScaledPow := ScaledIntegerPower.pow
def coordScaledComp := ScaledIntegerPower.comp

def coordScaledScaleBy (numerator : ℤ) (denominator : ℕ)
    (p : CoordScaledPower)
    (hdenominator : denominator ≠ 0 := by norm_num) : CoordScaledPower :=
  ScaledIntegerPower.scaleBy numerator denominator hdenominator p

def coordScaledZ : CoordScaledPower :=
  coordScaledInts [0, 1]

def coordScaledT : CoordScaledPower :=
  coordScaledComp
    (coordScaledRats 1000000000000
      [997224373628, -4138257629610, 11931757071320,
        -19405108055379, 12549969336367])
    (coordScaledRats 1000 [-387, 1000])

def coordScaledBlueFit : CoordScaledPower :=
  coordScaledRats 1000000000000
    [10835916271, 1160876492237, -1457602626354,
      1094952949203, -351563684247]

def coordScaledTaylorNine : CoordScaledPower :=
  coordScaledRats 362880
    [362880, -362880, 181440, -60480, 15120,
      -3024, 504, -72, 9, -1]

def coordScaledErrorTen : CoordScaledPower :=
  coordScaledRats 36288000
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11]

def coordScaledNewCorrection : CoordScaledPower :=
  coordScaledRats 200 [-50, 68, 39, -16]

def coordScaledQ : CoordScaledPower :=
  coordScaledSub
    (coordScaledNeg
      (coordScaledMul coordScaledNewCorrection coordScaledTaylorNine))
    (coordScaledScaleBy 1 4 coordScaledErrorTen)

def coordScaledR : CoordScaledPower :=
  coordScaledAdd coordScaledQ (coordScaledConstant 3 10)

def coordScaledExpSeries : CoordScaledPower :=
  coordScaledAdd
    (coordScaledAdd
      (coordScaledAdd (coordScaledInts [1]) coordScaledR)
      (coordScaledScaleBy 1 2 (coordScaledPow coordScaledR 2)))
    (coordScaledAdd
      (coordScaledScaleBy 1 6 (coordScaledPow coordScaledR 3))
      (coordScaledScaleBy 1 24 (coordScaledPow coordScaledR 4)))

def coordScaledExpPointThreeLower : CoordScaledPower :=
  let threeTenths := coordScaledConstant 3 10
  coordScaledSub
    (coordScaledComp coordScaledTaylorNine threeTenths)
    (coordScaledComp coordScaledErrorTen threeTenths)

def coordScaledExpQLower : CoordScaledPower :=
  coordScaledMul coordScaledExpPointThreeLower coordScaledExpSeries

def coordScaledBlueNumerator : CoordScaledPower :=
  coordScaledSub
    (coordScaledMul coordScaledZ coordScaledExpQLower)
    (coordScaledMul coordScaledBlueFit
      (coordScaledInts [1, 1]))

def coordScaledExpLowerFive : CoordScaledPower :=
  coordScaledRats 4320
    [4320, -4320, 2160, -720, 180, -36, -7]

def coordScaledMu : CoordScaledPower :=
  coordScaledMul coordScaledZ coordScaledExpLowerFive

def coordScaledOneMinusMu : CoordScaledPower :=
  coordScaledSub (coordScaledInts [1]) coordScaledMu

def coordScaledTBase : CoordScaledPower :=
  coordScaledMul coordScaledT
    (coordScaledPow
      (coordScaledAdd (coordScaledInts [1]) coordScaledT) 5)

def coordScaledDen : CoordScaledPower :=
  coordScaledMul coordScaledTBase coordScaledOneMinusMu

def coordScaledLogThreeNumerator : CoordScaledPower :=
  let t := coordScaledT
  coordScaledMul (coordScaledSub t (coordScaledInts [1]))
    (coordScaledAdd
      (coordScaledAdd
        (coordScaledAdd
          (coordScaledScaleBy 15 1 (coordScaledPow t 6))
          (coordScaledScaleBy 2 1 (coordScaledPow t 5)))
        (coordScaledAdd
          (coordScaledScaleBy 417 1 (coordScaledPow t 4))
          (coordScaledScaleBy 92 1 (coordScaledPow t 3))))
      (coordScaledAdd
        (coordScaledScaleBy 417 1 (coordScaledPow t 2))
        (coordScaledAdd
          (coordScaledScaleBy 2 1 t)
          (coordScaledInts [15]))))

def coordScaledCoordLogUpper (p : CoordScaledPower) : CoordScaledPower :=
  let s := coordScaledScaleBy 1 2
    (coordScaledSub (coordScaledInts [2]) p)
  coordScaledSub (coordScaledConstant 693147181 1000000000)
    (coordScaledComp
      (coordScaledRats 60 [0, 60, 30, 20, 15, 12, 10]) s)

def coordScaledOldCorrectionAtT : CoordScaledPower :=
  coordScaledComp
    (coordScaledRats 100 [-25, 41, 16, -8]) coordScaledT

def coordScaledTaylorFiveAtT : CoordScaledPower :=
  coordScaledComp
    (coordScaledRats 120 [120, -120, 60, -20, 5, -1])
    coordScaledT

def coordScaledErrorSixAtT : CoordScaledPower :=
  coordScaledComp
    (coordScaledRats 4320 [0, 0, 0, 0, 0, 0, 7])
    coordScaledT

def coordScaledBOther : CoordScaledPower :=
  coordScaledAdd
    (coordScaledCoordLogUpper
      (coordScaledAdd (coordScaledInts [1]) coordScaledT))
    (coordScaledAdd
      (coordScaledMul coordScaledOldCorrectionAtT
        coordScaledTaylorFiveAtT)
      (coordScaledScaleBy 1 4 coordScaledErrorSixAtT))

def coordScaledBLogNumerator : CoordScaledPower :=
  coordScaledSub
    (coordScaledScaleBy 1 30
      (coordScaledMul coordScaledLogThreeNumerator
        coordScaledOneMinusMu))
    (coordScaledMul coordScaledBOther coordScaledDen)

def coordScaledLogUpperFiveLoss
    (p : CoordScaledPower) : CoordScaledPower :=
  coordScaledNeg
    (coordScaledComp
      (coordScaledRats 60 [0, 60, 30, 20, 15, 12]) p)

def coordScaledBlueXTerm : CoordScaledPower :=
  coordScaledMul
    (coordScaledLogUpperFiveLoss coordScaledBlueFit)
    coordScaledTBase

def coordScaledMuXTerm : CoordScaledPower :=
  coordScaledMul
    (coordScaledLogUpperFiveLoss coordScaledMu) coordScaledDen

def coordScaledXLogNumerator : CoordScaledPower :=
  coordScaledAdd coordScaledBlueXTerm coordScaledMuXTerm

def coordScaledMainNumerator : CoordScaledPower :=
  coordScaledSub coordScaledBLogNumerator coordScaledXLogNumerator

end

end BackwardCoordRound1Back1Certificate
end Arxiv2407_19026
