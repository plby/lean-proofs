import Util.MaynardBFT.LargeFiberDiagonalLimit
import ErdosProblems.Erdos6.GenericS2Restricted
import BoundedGaps.Maynard.ConcreteS1CrossBound

/-!
# Restricted-Y diagonal versus the full coordinate fiber
-/

namespace MaynardBFT.Sieve

open Erdos6.Maynard

open scoped BigOperators

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

def tupleCoordinateOneSquarePerturbationEnvelope
    (H : Finset ℕ) (R D : ℕ) (m : H) (B : ℝ) : ℝ :=
  2 * (B * BoundedGaps.Maynard.preSievedCoordinateInvTotientMass
        (primorial D) R +
    B * ((Finset.univ.erase m).card : ℝ) *
      (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
        (1 + Real.log R)) *
      (8 / (D : ℝ) +
        (8 * Real.exp 8 / (D : ℝ)) *
          (1 + 8 * Real.exp 8 / (D : ℝ)) ^
            ((Finset.univ.erase m).card - 1))) *
    (B * ((Finset.univ.erase m).card : ℝ) *
      (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
        (1 + Real.log R)) *
      (8 / (D : ℝ) +
        (8 * Real.exp 8 / (D : ℝ)) *
          (1 + 8 * Real.exp 8 / (D : ℝ)) ^
            ((Finset.univ.erase m).card - 1)))

def tupleCoordinateOneSquarePerturbation (H : Finset ℕ) (alpha : ℝ)
    (N : ℕ) (m : H) : ℝ :=
  ∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H
      (maynardRadius alpha N) (maynardModulus N)).filter (fun r => r m = 1),
    tupleCoordinateOneSquarePerturbationEnvelope H (maynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m 1 /
      |∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)|

theorem abs_tupleRestrictedYTerm_sub_fiberTerm_le
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R (primorial D) y)
    (m : H) {r : H → ℕ} (hD : 0 < D)
    (hWL : (primorial D : ℝ) ≤ 1 + Real.log R)
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) {B : ℝ} (hB : 0 ≤ B)
    (hyBound : ∀ u, |y u| ≤ B) :
    |(BoundedGaps.Maynard.maynardS2RestrictedYFromCoefficients H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H R (primorial D))
          (BoundedGaps.Maynard.maynardCoefficientFromY H R (primorial D) y)
          m r) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) -
      (BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          y m r) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)| ≤
      tupleCoordinateOneSquarePerturbationEnvelope H R D m B /
        |∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)| := by
  let Y := BoundedGaps.Maynard.maynardS2RestrictedYFromCoefficients H
    (BoundedGaps.Maynard.maynardDivisorTupleSupport H R (primorial D))
    (BoundedGaps.Maynard.maynardCoefficientFromY H R (primorial D) y) m r
  let F := BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R
    (primorial D) y m r
  let g := ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)
  have hpoint :=
    BoundedGaps.Maynard.abs_maynardS2RestrictedY_sq_sub_coordinateFiber_sq_le_log
      hy m hD hWL hr hrm hB hyBound
  rw [show Y ^ 2 / g - F ^ 2 / g = (Y ^ 2 - F ^ 2) / g by ring,
    abs_div]
  exact div_le_div_of_nonneg_right (by
    simpa [Y, F, tupleCoordinateOneSquarePerturbationEnvelope] using hpoint)
    (abs_nonneg _)

theorem abs_tupleRestrictedYSum_sub_fiberSum_le
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R (primorial D) y)
    (m : H) (hD : 0 < D)
    (hWL : (primorial D : ℝ) ≤ 1 + Real.log R)
    {B : ℝ} (hB : 0 ≤ B) (hyBound : ∀ u, |y u| ≤ B) :
    |(∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H R
          (primorial D)).filter (fun r => r m = 1),
        (BoundedGaps.Maynard.maynardS2RestrictedYFromCoefficients H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H R (primorial D))
          (BoundedGaps.Maynard.maynardCoefficientFromY H R (primorial D) y)
          m r) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)) -
      (∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H R
          (primorial D)).filter (fun r => r m = 1),
        (BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          y m r) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ))| ≤
      ∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H R
          (primorial D)).filter (fun r => r m = 1),
        tupleCoordinateOneSquarePerturbationEnvelope H R D m B /
          |∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H R
          (primorial D)).filter (fun r => r m = 1),
        |(BoundedGaps.Maynard.maynardS2RestrictedYFromCoefficients H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H R (primorial D))
          (BoundedGaps.Maynard.maynardCoefficientFromY H R (primorial D) y)
          m r) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) -
        (BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          y m r) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      have hrData := Finset.mem_filter.mp hr
      exact abs_tupleRestrictedYTerm_sub_fiberTerm_le hy m hD hWL
        (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hrData.1)
        hrData.2 hB hyBound

theorem tupleCoordinateOneYDiagonal_eq_explicit
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ) (N : ℕ) (m : H) :
    tupleCoordinateOneYDiagonal H alpha F N m =
      ∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H
          (maynardRadius alpha N) (maynardModulus N)).filter
          (fun r => r m = 1),
        (BoundedGaps.Maynard.maynardS2RestrictedYFromCoefficients H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H
            (maynardRadius alpha N) (maynardModulus N))
          (BoundedGaps.Maynard.maynardCoefficientFromY H
            (maynardRadius alpha N) (maynardModulus N)
            (BoundedGaps.Maynard.maynardYValue H (maynardRadius alpha N)
              (maynardModulus N) F)) m r) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) := by
  unfold tupleCoordinateOneYDiagonal tupleMaynardCoefficient
  congr 1
  funext d
  exact BoundedGaps.Maynard.maynardCoefficient_eq_fromYValue _ _ _ _ d

theorem abs_tupleCoordinateOneYDiagonal_sub_fiberSquareDiagonal_le
    {H : Finset ℕ} {alpha : ℝ} (N : ℕ) (m : H)
    (hD : 0 < BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (maynardModulus N : ℝ) ≤ 1 + Real.log (maynardRadius alpha N)) :
    |tupleCoordinateOneYDiagonal H alpha (tupleLargeCandidate H) N m -
        tupleCoordinateFiberSquareDiagonal H alpha N m| ≤
      tupleCoordinateOneSquarePerturbation H alpha N m := by
  let R := maynardRadius alpha N
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := primorial D
  let S := (BoundedGaps.Maynard.maynardDivisorTupleSupport H R W).filter
    (fun r => r m = 1)
  let y := BoundedGaps.Maynard.maynardYValue H R W (tupleLargeCandidate H)
  let Y : (H → ℕ) → ℝ := fun r =>
    BoundedGaps.Maynard.maynardS2RestrictedYFromCoefficients H
      (BoundedGaps.Maynard.maynardDivisorTupleSupport H R W)
      (BoundedGaps.Maynard.maynardCoefficientFromY H R W y) m r
  let F : (H → ℕ) → ℝ := fun r =>
    BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R W y m r
  have hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y :=
    BoundedGaps.Maynard.isSupportedMaynardY_maynardYValue _ _ _ _
  have hyBound : ∀ r, |y r| ≤ (1 : ℝ) := by
    intro r
    exact BoundedGaps.Maynard.abs_maynardYValue_le H R W
      (tupleLargeCandidate H) (by norm_num)
      (tupleLargeCandidate_abs_le_one H) r
  have hD' : 0 < D := by simpa [D] using hD
  have hWL' : (W : ℝ) ≤ 1 + Real.log R := by
    simpa [W, R, D, maynardModulus,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using hWL
  have hsum := abs_tupleRestrictedYSum_sub_fiberSum_le hy m hD' hWL'
    (B := (1 : ℝ)) (by norm_num) hyBound
  rw [tupleCoordinateOneYDiagonal_eq_explicit]
  unfold tupleCoordinateFiberSquareDiagonal
    tupleCoordinateOneSquarePerturbation
  simpa only [R, D, W, S, y, Y, F, maynardRadius, maynardModulus,
    BoundedGaps.Maynard.engelsmaMaynardModulus] using hsum

end

end MaynardBFT.Sieve
