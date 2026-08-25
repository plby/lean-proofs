import ErdosProblems.Erdos237b.S2TransformBounds
import BoundedGaps.Maynard.MaynardS2YFaceSupport

/-!
# Transfer from the restricted S2 diagonal to squared coordinate fibers

This comparison is uniform over bounded supported Y-weights and has a
vanishing normalized error, with the pre-sieve density retained throughout.
-/

namespace Erdos237b

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

noncomputable def s2FiberSquareDiagonal (H : Finset ℕ) (R W : ℕ)
    (y : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ r ∈ (maynardDivisorTupleSupport H R W).filter (fun r => r m = 1),
    maynardS2CoordinateFiberSum H R W y m r ^ 2 / ∏ h : H, (maynardS2G (r h) : ℝ)

noncomputable def s2SquareErrorEnvelope (k R D : ℕ) (B : ℝ) : ℝ :=
  (B * squarefreeCoprimeInvTotientMean (primorial D) R) ^ 2 *
    ((k : ℝ) * s2FiberErrorFactor k D) * ((k : ℝ) * s2FiberErrorFactor k D + 2)

theorem s2SquareErrorEnvelope_nonneg (k R D : ℕ) (B : ℝ) :
    0 ≤ s2SquareErrorEnvelope k R D B := by
  have := s2FiberErrorFactor_nonneg k D
  unfold s2SquareErrorEnvelope
  positivity

theorem abs_sq_sub_sq_le_from_difference {a b E M : ℝ}
    (hE : 0 ≤ E) (_hM : 0 ≤ M) (hd : |a - b| ≤ E) (hb : |b| ≤ M) :
    |a ^ 2 - b ^ 2| ≤ E * (E + 2 * M) := by
  have hab : |a + b| ≤ E + 2 * M := by
    calc
      _ = |(a - b) + 2 * b| := by congr 1; ring
      _ ≤ |a - b| + |2 * b| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; gcongr
  calc
    _ = |a - b| * |a + b| := by rw [← abs_mul]; congr 1; ring
    _ ≤ _ := mul_le_mul hd hab (abs_nonneg _) hE

theorem abs_s2Transform_sq_sub_fiber_sq_le {H : Finset ℕ} {R D : ℕ}
    {y : (H → ℕ) → ℝ} (hy : IsSupportedMaynardY H R (primorial D) y)
    (m : H) {r : H → ℕ} (hD : 0 < D)
    (hr : IsMaynardDivisorTuple H R (primorial D) r) (hrm : r m = 1)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ u, |y u| ≤ B) :
    |maynardS2RestrictedYFromCoefficients H (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y) m r ^ 2 -
      maynardS2CoordinateFiberSum H R (primorial D) y m r ^ 2| ≤
      s2SquareErrorEnvelope (univ.erase m).card R D B := by
  have hM := mul_nonneg hB (squarefreeCoprimeInvTotientMean_nonneg (primorial D) R)
  have hE := s2FiberErrorFactor_nonneg (univ.erase m).card D
  have h := abs_sq_sub_sq_le_from_difference (by positivity) hM
    (abs_s2Transform_sub_fiber_le_mean hy m hD hr hrm hB hbound)
    (abs_s2Fiber_le_mean (R := R) (D := D) m r hB hbound)
  apply h.trans_eq
  unfold s2SquareErrorEnvelope
  ring

theorem coordinateOne_reciprocalG_mass_le {H : Finset ℕ} (R W : ℕ) (m : H) :
    (∑ r ∈ (maynardDivisorTupleSupport H R W).filter (fun r => r m = 1),
      (1 : ℝ) / ∏ h : H, (maynardS2G (r h) : ℝ)) ≤
      maynardS2ReciprocalGSquarefreeMean W R ^ (univ.erase m).card := by
  classical
  apply le_trans ?_ restrictedS2CommonReciprocalGMass_le
  apply sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro r hr
  obtain ⟨hr, hrm⟩ := mem_filter.mp hr
  have ht := isMaynardDivisorTuple_of_mem_support hr
  rw [restrictedS2CommonCoordinateOneBox, Fintype.mem_piFinset]
  intro h
  by_cases hh : h = m
  · subst h
    simp [hrm]
  · rw [if_neg hh, preSievedCommonCoordinateSupport, mem_filter]
    have hb := (mem_maynardDivisorTupleBox_iff.mp ht.mem_maynardDivisorTupleBox) h
    exact ⟨mem_range.mpr hb.2, hb.1, ht.coordinate_squarefree h, ht.coordinate_coprime_W h⟩

theorem abs_s2Diagonal_sub_fiberDiagonal_le {H : Finset ℕ} {R D : ℕ}
    {y : (H → ℕ) → ℝ} (hy : IsSupportedMaynardY H R (primorial D) y)
    (m : H) (hD : 0 < D) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ u, |y u| ≤ B) :
    |maynardS2RestrictedYDiagonalSum H R (primorial D)
        (maynardCoefficientFromY H R (primorial D) y) m -
      s2FiberSquareDiagonal H R (primorial D) y m| ≤
      s2SquareErrorEnvelope (univ.erase m).card R D B *
        maynardS2ReciprocalGSquarefreeMean (primorial D) R ^ (univ.erase m).card := by
  classical
  rw [maynardS2RestrictedYDiagonalSum_eq_coordinateOne]
  unfold maynardS2RestrictedYCoordinateOneDiagonalSum s2FiberSquareDiagonal
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ (maynardDivisorTupleSupport H R (primorial D)).filter (fun r => r m = 1),
        |maynardS2RestrictedYFromCoefficients H
            (maynardDivisorTupleSupport H R (primorial D))
            (maynardCoefficientFromY H R (primorial D) y) m r ^ 2 /
              (∏ h : H, (maynardS2G (r h) : ℝ)) -
          maynardS2CoordinateFiberSum H R (primorial D) y m r ^ 2 /
              (∏ h : H, (maynardS2G (r h) : ℝ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ (maynardDivisorTupleSupport H R (primorial D)).filter (fun r => r m = 1),
        s2SquareErrorEnvelope (univ.erase m).card R D B *
          (1 / ∏ h : H, (maynardS2G (r h) : ℝ)) := by
      apply sum_le_sum
      intro r hr
      obtain ⟨hr, hrm⟩ := mem_filter.mp hr
      rw [← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤
        ∏ h : H, (maynardS2G (r h) : ℝ) by positivity), mul_one_div]
      exact div_le_div_of_nonneg_right
        (abs_s2Transform_sq_sub_fiber_sq_le hy m hD
          (isMaynardDivisorTuple_of_mem_support hr) hrm hB hbound) (by positivity)
    _ = s2SquareErrorEnvelope (univ.erase m).card R D B *
        ∑ r ∈ (maynardDivisorTupleSupport H R (primorial D)).filter (fun r => r m = 1),
          (1 / ∏ h : H, (maynardS2G (r h) : ℝ)) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (coordinateOne_reciprocalG_mass_le R (primorial D) m)
      (s2SquareErrorEnvelope_nonneg _ _ _ _)

theorem tendsto_s2SquareErrorEnvelope_div_scale_sq (k : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (B : ℝ) :
    Tendsto (fun N : ℕ => s2SquareErrorEnvelope k (engelsmaMaynardRadius alpha N)
      (tripleLogCutoff (N - 1)) B / sieveCoordinateScale alpha N ^ 2) atTop (nhds 0) := by
  have hmean := ((tendsto_mean_div_sieveCoordinateScale halpha).const_mul B).pow 2
  have hfac := (tendsto_s2FiberErrorFactor k).const_mul (k : ℝ)
  have hlim := (hmean.mul hfac).mul (hfac.add_const 2)
  simp only [mul_zero, zero_mul] at hlim
  apply hlim.congr'
  filter_upwards [] with N
  unfold s2SquareErrorEnvelope
  simp only [engelsmaMaynardModulus]
  ring

theorem tendsto_normalized_s2Diagonal_sub_fiberDiagonal {H : Finset ℕ} {alpha B : ℝ}
    (halpha : 0 < alpha) (hB : 0 ≤ B) (y : ℕ → (H → ℕ) → ℝ)
    (hy : ∀ N, IsSupportedMaynardY H (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) (y N))
    (hbound : ∀ N r, |y N r| ≤ B) (m : H) :
    Tendsto (fun N : ℕ =>
      (maynardS2RestrictedYDiagonalSum H (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N) (maynardCoefficientFromY H
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) (y N)) m -
        s2FiberSquareDiagonal H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) (y N) m) /
        sieveCoordinateScale alpha N ^ ((univ.erase m).card + 2))
      atTop (nhds 0) := by
  let k := (univ.erase m).card
  have hE := tendsto_s2SquareErrorEnvelope_div_scale_sq k halpha B
  have hmean : Tendsto (fun N : ℕ =>
      (maynardS2ReciprocalGSquarefreeMean (engelsmaMaynardModulus N)
        (engelsmaMaynardRadius alpha N) / sieveCoordinateScale alpha N) ^ k)
      atTop (nhds 1) := by
    simpa [sieveCoordinateScale] using
      (tendsto_engelsmaReciprocalGSquarefreeMean_div_leadingTerm_one halpha).pow k
  have hlim := hE.mul hmean
  simp only [zero_mul] at hlim
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_sieveCoordinateScale_pos halpha,
    tendsto_shifted_tripleLogCutoff.eventually_gt_atTop 0] with N hA hD
  have hb := abs_s2Diagonal_sub_fiberDiagonal_le (hy N) m hD hB (hbound N)
  have hd := div_le_div_of_nonneg_right hb (pow_nonneg hA.le (k + 2))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hA _)]
  convert hd using 1
  all_goals try rfl
  simp only [div_pow, pow_add, k, engelsmaMaynardModulus]
  ring

end Erdos237b
