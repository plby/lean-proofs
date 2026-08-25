import Util.MaynardTao.BFT.LargeFiberFactor
import ErdosProblems.Erdos6.GenericRestrictedYPerturbationLimit
import BoundedGaps.Maynard.MaynardS2RestrictedStarredCorrectionBound

/-!
# Generic finite bound for the restricted S2 cross correction
-/

namespace MaynardBFT.Sieve

open Erdos6.Maynard

open scoped BigOperators

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

def tupleRestrictedTransformEnvelope
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) (m : H) : ℝ :=
  (8 * ((Nat.totient (maynardModulus N) : ℝ) / maynardModulus N) *
      (1 + Real.log (maynardRadius alpha N))) *
    (1 + ((Finset.univ.erase m).card : ℝ) *
      (8 / (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ) +
        (8 * Real.exp 8 /
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) *
          (1 + 8 * Real.exp 8 /
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) ^
              ((Finset.univ.erase m).card - 1)))

theorem tupleRestrictedTransformEnvelope_nonneg
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ} {m : H}
    (hD : 0 < BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (maynardModulus N : ℝ) ≤
      1 + Real.log (maynardRadius alpha N)) :
    0 ≤ tupleRestrictedTransformEnvelope H alpha N m := by
  have hlog : 0 ≤ 1 + Real.log (maynardRadius alpha N) :=
    (Nat.cast_nonneg (maynardModulus N)).trans hWL
  have hDreal : (0 : ℝ) <
      BoundedGaps.Maynard.tripleLogCutoff (N - 1) := by exact_mod_cast hD
  unfold tupleRestrictedTransformEnvelope
  positivity

theorem abs_tupleRestrictedY_le_transformEnvelope
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ} (m : H) {r : H → ℕ}
    (hD : 0 < BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (maynardModulus N : ℝ) ≤
      1 + Real.log (maynardRadius alpha N))
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H
      (maynardRadius alpha N) (maynardModulus N) r)
    (hrm : r m = 1) :
    |BoundedGaps.Maynard.maynardS2RestrictedYFromCoefficients H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H
          (maynardRadius alpha N) (maynardModulus N))
        (BoundedGaps.Maynard.maynardCoefficientFromY H
          (maynardRadius alpha N) (maynardModulus N)
          (BoundedGaps.Maynard.maynardYValue H
            (maynardRadius alpha N) (maynardModulus N)
            (tupleLargeCandidate H))) m r| ≤
      tupleRestrictedTransformEnvelope H alpha N m := by
  have h := BoundedGaps.Maynard.abs_maynardS2RestrictedY_le_log
    (BoundedGaps.Maynard.isSupportedMaynardY_maynardYValue H
      (maynardRadius alpha N) (maynardModulus N) (tupleLargeCandidate H))
    m hD hWL hr hrm (show (0 : ℝ) ≤ 1 by norm_num)
    (fun u => BoundedGaps.Maynard.abs_maynardYValue_le H
      (maynardRadius alpha N) (maynardModulus N) (tupleLargeCandidate H)
      (by norm_num) (tupleLargeCandidate_abs_le_one H) u)
  simpa [tupleRestrictedTransformEnvelope, maynardModulus,
    BoundedGaps.Maynard.engelsmaMaynardModulus] using h

theorem abs_tupleRestrictedCross_le_explicit
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ} (m : H)
    (hR : 1 < maynardRadius alpha N)
    (hD : 2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (maynardModulus N : ℝ) ≤
      1 + Real.log (maynardRadius alpha N)) :
    |tupleRestrictedCross H alpha (tupleLargeCandidate H) N m| ≤
      tupleRestrictedTransformEnvelope H alpha N m ^ 2 *
        ((32 * Real.exp 32 /
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) *
          ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (Real.exp 32) ^
            ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)) *
        (BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
          (maynardModulus N) (maynardRadius alpha N)) ^
            (Finset.univ.erase m).card := by
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := maynardRadius alpha N
  let W := maynardModulus N
  let y := BoundedGaps.Maynard.maynardYValue H R W (tupleLargeCandidate H)
  let E := tupleRestrictedTransformEnvelope H alpha N m
  let T := BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail H D R
  let M := BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean W R
  have hcoeff : tupleMaynardCoefficient H alpha (tupleLargeCandidate H) N =
      BoundedGaps.Maynard.maynardCoefficientFromY H R W y := by
    funext d
    exact BoundedGaps.Maynard.maynardCoefficient_eq_fromYValue _ _ _ _ d
  have hbase : |tupleRestrictedCross H alpha (tupleLargeCandidate H) N m| ≤
      E ^ 2 * T *
        BoundedGaps.Maynard.restrictedS2CommonReciprocalGMass H W R m := by
    unfold tupleRestrictedCross
    rw [hcoeff]
    apply BoundedGaps.Maynard.abs_incompatibleRestrictedS2_le_crossTail_mul_commonMass
      hR hD (tupleRestrictedTransformEnvelope_nonneg
        (Nat.zero_lt_of_lt hD) hWL)
    intro r hr hrm
    exact abs_tupleRestrictedY_le_transformEnvelope m
      (Nat.zero_lt_of_lt hD) hWL hr hrm
  have htail0 : 0 ≤ T := by
    unfold T BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail
    exact Finset.sum_nonneg fun s hs => by
      unfold BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareWeight
      exact Finset.prod_nonneg fun x hx =>
        Finset.prod_nonneg fun p hp =>
          BoundedGaps.Maynard.maynardS2CrossPrimeSquareWeight_nonneg p
  have hM0 : 0 ≤ M := by
    unfold M BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
    exact Finset.sum_nonneg fun n hn =>
      tupleReciprocalGSquarefreeAF_nonneg _ n
  have hmass := BoundedGaps.Maynard.restrictedS2CommonReciprocalGMass_le
    (H := H) (W := W) (R := R) (m := m)
  have htail := BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail_le
    (H := H) (Q := R) hD
  calc
    _ ≤ E ^ 2 * T *
        BoundedGaps.Maynard.restrictedS2CommonReciprocalGMass H W R m := hbase
    _ ≤ E ^ 2 * T * M ^ (Finset.univ.erase m).card :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg (sq_nonneg _) htail0)
    _ ≤ E ^ 2 *
        ((32 * Real.exp 32 / (D : ℝ)) *
          ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (Real.exp 32) ^
            ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)) *
          M ^ (Finset.univ.erase m).card :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail (sq_nonneg _))
        (pow_nonneg hM0 _)
    _ = _ := by rfl

end

end MaynardBFT.Sieve
