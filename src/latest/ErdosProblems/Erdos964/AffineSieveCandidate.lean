import ErdosProblems.Erdos964.AffineSieveS1
import ErdosProblems.Erdos964.SievePolynomial
import BoundedGaps.Maynard.MaynardLambdaSharpBound
import BoundedGaps.Maynard.MaynardSupportBounds

/-!
# Concrete bounded coefficients for the affine sieve

Use the radial function from the integral certificate on the simplex and
zero elsewhere. The first arithmetic error has a uniform explicit bound.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

noncomputable def radialSieveCandidate (H : Finset ℕ) (t : H → ℝ) : ℝ := by
  classical
  exact if (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 then linearSieveWeight (∑ i, t i) else 0

theorem radialSieveCandidate_abs_le (H : Finset ℕ) (t : H → ℝ) :
    |radialSieveCandidate H t| ≤ 7 := by
  classical
  unfold radialSieveCandidate
  split_ifs with ht
  · have hsum : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _ => ht.1 i)
    change |7 - 6 * ∑ i, t i| ≤ 7
    rw [abs_le]
    constructor <;> linarith [ht.2]
  · norm_num

noncomputable def affineMaynardWeight {H : Finset ℕ} (A B : H → ℕ)
    (R W v n : ℕ) : ℝ :=
  affineSquareSieveWeight A B (maynardDivisorTupleSupport H R W)
    (maynardCoefficient H R W (radialSieveCandidate H)) v W n

noncomputable def affineMaynardS1Main (H : Finset ℕ) (R W N : ℕ) : ℝ :=
  (N : ℝ) / W * compatibleDivisorPairNormalizedMainSum H
    (maynardDivisorTupleSupport H R W) (maynardCoefficient H R W (radialSieveCandidate H))

theorem affineMaynardWeight_nonneg {H : Finset ℕ} (A B : H → ℕ) (R W v n : ℕ) :
    0 ≤ affineMaynardWeight A B R W v n :=
  affineSquareSieveWeight_nonneg A B _ _ v W n

theorem radialSieveCoefficient_abs_le {H : Finset ℕ} (hH : H.Nonempty)
    (R W : ℕ) (d : H → ℕ) (hd : d ∈ maynardDivisorTupleSupport H R W) :
    |maynardCoefficient H R W (radialSieveCandidate H) d| ≤
      7 * (1 + Real.log R) ^ (2 * (Fintype.card H) ^ 2) :=
  abs_maynardCoefficient_le_sharp_log H R W (radialSieveCandidate H) d 7
    (by norm_num) (radialSieveCandidate_abs_le H) hH hd

theorem affineMaynardS1_error_le_log_envelope
    {H : Finset ℕ} (hH : H.Nonempty) (A B : H → ℕ) (R W v N : ℕ) (hW : 0 < W)
    (hlead : CoversAffineLeadingPrimes A W) (hdet : CoversAffineDeterminantPrimes A B W) :
    |(∑ n ∈ Finset.Ico N (2 * N), affineMaynardWeight A B R W v n) -
        affineMaynardS1Main H R W N| ≤
      ((R : ℝ) * (1 + Real.log R) ^ Fintype.card H) ^ 2 *
        (7 * (1 + Real.log R) ^ (2 * (Fintype.card H) ^ 2)) ^ 2 := by
  have hlog : 0 ≤ 1 + Real.log (R : ℝ) := by
    linarith [Real.log_natCast_nonneg R]
  have herror := affineSieveWeightSum_sub_main_le_coefficientMass A B
    (maynardDivisorTupleSupport H R W) (maynardCoefficient H R W (radialSieveCandidate H))
    v N hW (fun _ hd => isMaynardDivisorTuple_of_mem_support hd) hlead hdet
  have hmass := compatibleDivisorPairCoefficientMass_le_card_sq_mul
    (by positivity : 0 ≤ 7 * (1 + Real.log (R : ℝ)) ^ (2 * (Fintype.card H) ^ 2))
    (radialSieveCoefficient_abs_le hH R W)
  have hcard := pow_le_pow_left₀ (Nat.cast_nonneg _)
    (maynardDivisorTupleSupport_card_le_log H R W) 2
  exact (herror.trans hmass).trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))

theorem affineMaynardS1_three_error_le
    {H : Finset ℕ} (hH : H.card = 3) (A B : H → ℕ) (R W v N : ℕ) (hW : 0 < W)
    (hlead : CoversAffineLeadingPrimes A W) (hdet : CoversAffineDeterminantPrimes A B W) :
    |(∑ n ∈ Finset.Ico N (2 * N), affineMaynardWeight A B R W v n) -
        affineMaynardS1Main H R W N| ≤
      49 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ 42 := by
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  have hbound := affineMaynardS1_error_le_log_envelope hHne A B R W v N hW hlead hdet
  have hcard : Fintype.card H = 3 := by simpa only [Fintype.card_coe] using hH
  rw [hcard] at hbound
  convert hbound using 1
  ring

end Erdos964
