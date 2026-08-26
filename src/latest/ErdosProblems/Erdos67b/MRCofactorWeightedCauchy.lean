import ErdosProblems.Erdos67b.MRGSA10WeightedVerticalCauchy

/-!
# Weighted vertical Cauchy with a bounded cofactor

The low/high cofactor is bounded in the weighted energy, leaving one
Perron denominator in each of the two Mangoldt energies.
-/

open Complex MeasureTheory Set

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrWeightedVerticalEnergy_nonneg (F : ℝ → ℂ) (sigma : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ gsA10WeightedVerticalEnergy F sigma (-T) T := by
  unfold gsA10WeightedVerticalEnergy
  exact intervalIntegral.integral_nonneg (by linarith)
    (fun t _ ↦ mul_nonneg (gsA10VerticalPerronWeight_nonneg sigma t) (normSq_nonneg _))

theorem mrWeightedVerticalEnergy_comp_neg (F : ℝ → ℂ) (sigma T : ℝ) :
    gsA10WeightedVerticalEnergy (fun t ↦ F (-t)) sigma (-T) T =
      gsA10WeightedVerticalEnergy F sigma (-T) T := by
  have h := intervalIntegral.integral_comp_neg (a := -T) (b := T)
    (f := fun t ↦ gsA10VerticalPerronWeight sigma t * normSq (F t))
  simpa only [gsA10WeightedVerticalEnergy, gsA10VerticalPerronWeight, neg_sq, neg_neg] using h

theorem mrWeightedVerticalEnergy_mul_le
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    {sigma T M : ℝ} (hsigma : 0 < sigma) (hT : 0 ≤ T) (_hM : 0 ≤ M)
    (hbound : ∀ t, |t| ≤ T → ‖F t‖ ≤ M) :
    gsA10WeightedVerticalEnergy (fun t ↦ F t * G t) sigma (-T) T ≤
      M ^ 2 * gsA10WeightedVerticalEnergy G sigma (-T) T := by
  unfold gsA10WeightedVerticalEnergy
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact (continuous_gsA10WeightedVerticalIntegrand _ (hF.mul hG) hsigma).intervalIntegrable _ _
  · exact (continuous_const.mul
      (continuous_gsA10WeightedVerticalIntegrand G hG hsigma)).intervalIntegrable _ _
  · intro t ht
    have htT : |t| ≤ T := abs_le.mpr ht
    have hsq : normSq (F t) ≤ M ^ 2 := by
      rw [normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound t htT) 2
    rw [normSq_mul]
    calc
      _ ≤ gsA10VerticalPerronWeight sigma t * (M ^ 2 * normSq (G t)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsq (normSq_nonneg _))
          (gsA10VerticalPerronWeight_nonneg sigma t)
      _ = _ := by ring

theorem mrNorm_intervalIntegral_triple_div_vertical_le_weightedEnergy
    (F G H : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G) (hH : Continuous H)
    {sigma T M : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hbound : ∀ t, |t| ≤ T → ‖F t‖ ≤ M) :
    ‖∫ t in -T..T, F t * G t * H t / ((sigma : ℂ) + I * (t : ℂ))‖ ≤
      M * (gsA10WeightedVerticalEnergy G sigma (-T) T) ^ ((1 : ℝ) / 2) *
        (gsA10WeightedVerticalEnergy H sigma (-T) T) ^ ((1 : ℝ) / 2) := by
  have hbase := norm_intervalIntegral_mul_div_vertical_le_weightedEnergy
    (fun t ↦ F t * G t) H (hF.mul hG) hH hsigma hT
  have henergy := mrWeightedVerticalEnergy_mul_le F G hF hG
    (sigma := sigma) (T := T) (M := M) (by linarith) hT hM hbound
  have hpow := Real.rpow_le_rpow
    (mrWeightedVerticalEnergy_nonneg (fun t ↦ F t * G t) sigma hT) henergy
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hroot : (M ^ 2 * gsA10WeightedVerticalEnergy G sigma (-T) T) ^ ((1 : ℝ) / 2) =
      M * (gsA10WeightedVerticalEnergy G sigma (-T) T) ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow (sq_nonneg M) (mrWeightedVerticalEnergy_nonneg G sigma hT)]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hM]
  rw [hroot] at hpow
  exact hbase.trans (mul_le_mul_of_nonneg_right hpow
    (Real.rpow_nonneg (mrWeightedVerticalEnergy_nonneg H sigma hT) _))

end

end Erdos67b
