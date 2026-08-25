import ErdosProblems.Erdos237.S2TransformBounds

/-!
# Vanishing of the restricted S2 cross correction

The arithmetic cross-tail bound, reciprocal-g mean limit, and bounded
supported transform envelope give a generic result for each coordinate.
-/

namespace Erdos237

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

noncomputable def s2CrossTailConstant (H : Finset ℕ) : ℝ :=
  32 * Real.exp 32 * ((offDiagonalPairs H).card : ℝ) *
    Real.exp 32 ^ ((offDiagonalPairs H).card - 1)

theorem s2CrossTailConstant_nonneg (H : Finset ℕ) : 0 ≤ s2CrossTailConstant H := by
  unfold s2CrossTailConstant
  positivity

theorem abs_s2Cross_le_mean {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R (primorial D) y) (m : H) (hR : 1 < R) (hD : 2 ≤ D)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ u, |y u| ≤ B) :
    |incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum H
      (maynardDivisorTupleSupport H R (primorial D))
      (maynardCoefficientFromY H R (primorial D) y) m| ≤
      s2TransformEnvelope (univ.erase m).card R D B ^ 2 * (s2CrossTailConstant H / D) *
        maynardS2ReciprocalGSquarefreeMean (primorial D) R ^ (univ.erase m).card := by
  have hE := s2TransformEnvelope_nonneg (univ.erase m).card R D hB
  have ht : roughS2CrossTupleReciprocalGSquareTail H D R ≤ s2CrossTailConstant H / D := by
    convert roughS2CrossTupleReciprocalGSquareTail_le (H := H) (Q := R) hD using 1
    unfold s2CrossTailConstant
    ring
  have hmass : 0 ≤ restrictedS2CommonReciprocalGMass H (primorial D) R m := by
    unfold restrictedS2CommonReciprocalGMass commonS2GProduct
    positivity
  calc
    _ ≤ s2TransformEnvelope (univ.erase m).card R D B ^ 2 *
        roughS2CrossTupleReciprocalGSquareTail H D R *
        restrictedS2CommonReciprocalGMass H (primorial D) R m :=
      abs_incompatibleRestrictedS2_le_crossTail_mul_commonMass hR hD hE
        (fun _ hr hrm => abs_s2Transform_le_envelope hy m (by omega) hr hrm hB hbound)
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left ht (sq_nonneg _))
      restrictedS2CommonReciprocalGMass_le hmass
        (mul_nonneg (sq_nonneg _) (div_nonneg (s2CrossTailConstant_nonneg H) (by positivity)))

theorem tendsto_normalized_s2_cross {H : Finset ℕ} {alpha B : ℝ}
    (halpha : 0 < alpha) (hB : 0 ≤ B) (y : ℕ → (H → ℕ) → ℝ)
    (hy : ∀ N, IsSupportedMaynardY H (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) (y N))
    (hbound : ∀ N r, |y N r| ≤ B) (m : H) :
    Tendsto (fun N : ℕ =>
      incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum H
        (maynardDivisorTupleSupport H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N))
        (maynardCoefficientFromY H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) (y N)) m /
        sieveCoordinateScale alpha N ^ ((univ.erase m).card + 2))
      atTop (nhds 0) := by
  let k := (univ.erase m).card
  have hE := (tendsto_s2TransformEnvelope_div_scale k halpha B).pow 2
  have htail : Tendsto (fun N : ℕ => s2CrossTailConstant H / tripleLogCutoff (N - 1))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (s2CrossTailConstant H)).comp
      tendsto_shifted_tripleLogCutoff
  have hmean : Tendsto (fun N : ℕ =>
      (maynardS2ReciprocalGSquarefreeMean (engelsmaMaynardModulus N)
        (engelsmaMaynardRadius alpha N) / sieveCoordinateScale alpha N) ^ k)
      atTop (nhds 1) := by
    simpa [sieveCoordinateScale] using
      (tendsto_engelsmaReciprocalGSquarefreeMean_div_leadingTerm_one halpha).pow k
  have hlim := (hE.mul htail).mul hmean
  simp only [mul_zero, zero_mul] at hlim
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_sieveCoordinateScale_pos halpha,
    eventually_one_lt_engelsmaMaynardRadius halpha,
    tendsto_shifted_tripleLogCutoff.eventually_ge_atTop 2] with N hA hR hD
  have hb := abs_s2Cross_le_mean (hy N) m hR hD hB (hbound N)
  have hd := div_le_div_of_nonneg_right hb (pow_nonneg hA.le (k + 2))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hA _)]
  convert hd using 1
  all_goals try rfl
  simp only [div_pow, pow_add, k, engelsmaMaynardModulus]
  ring

end Erdos237
