/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCubeMoment
import ErdosProblems.Erdos4b.FGKMTProfileMoment

/-!
# The coupled profile retains a fixed fraction of the tensor energy

The proof is the integral form of Markov's inequality. The numerical
moment condition is explicit and will be verified for the chosen
dimension-dependent scales; it is not an assumption of the final
prime-gap theorem.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

theorem sieveCutoff_sq_lower {s : ℝ} (hs : 0 ≤ s) :
    1 - (10 / 9) * s ≤ sieveCutoff s ^ 2 := by
  by_cases hs' : s ≤ 9 / 10
  · rw [sieveCutoff_one_of_le hs']
    nlinarith
  · nlinarith [sq_nonneg (sieveCutoff s)]

theorem sieveCutoff_sq_le_one (s : ℝ) : sieveCutoff s ^ 2 ≤ 1 := by
  have h0 := sieveCutoff_nonneg s
  have h1 := sieveCutoff_le_one s
  nlinarith

theorem cutoffCubeIntegral_sieveCutoff_sq_upper {G : ℝ → ℝ} (hG : Continuous G)
    (hG0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G t) (j : ℕ) :
    cutoffCubeIntegral G (fun s => sieveCutoff s ^ 2) j 0 ≤ (∫ t in (0 : ℝ)..1, G t) ^ j := by
  obtain ⟨K, hK, hψ⟩ := exists_sieveCutoff_bounded
  have hI := cutoffCubeIntegrand_integrable hG (sieveCutoff_sq_bounded hK hψ) j 0
  have hGi : Integrable G unitIntervalMeasure := hG.integrableOn_Icc
  have hprod := Integrable.fintype_prod (fun _ : Fin j => hGi)
  unfold cutoffCubeIntegral
  calc
    _ ≤ ∫ t : Fin j → ℝ, ∏ i, G (t i)
        ∂Measure.pi (fun _ : Fin j => unitIntervalMeasure) :=
      integral_mono_ae hI hprod (by
        filter_upwards [ae_unitCube j] with t ht
        have hprod0 : 0 ≤ ∏ i, G (t i) := Finset.prod_nonneg (fun i _hi => hG0 _ (ht i))
        change (∏ i, G (t i)) * sieveCutoff (0 + ∑ i, t i) ^ 2 ≤ ∏ i, G (t i)
        calc
          _ ≤ (∏ i, G (t i)) * 1 :=
            mul_le_mul_of_nonneg_left (sieveCutoff_sq_le_one _) hprod0
          _ = _ := mul_one _)
    _ = _ := by
      rw [integral_fintype_prod_eq_pow]
      simp only [Fintype.card_fin, unitIntervalMeasure_integral]

theorem cutoffCubeIntegral_sieveCutoff_sq_lower {G : ℝ → ℝ} (hG : Continuous G)
    (hG0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G t) (j : ℕ) :
    (∫ t in (0 : ℝ)..1, G t) ^ j -
      (10 / 9) * (j : ℝ) * (∫ t in (0 : ℝ)..1, t * G t) *
        (∫ t in (0 : ℝ)..1, G t) ^ (j - 1) ≤
      cutoffCubeIntegral G (fun s => sieveCutoff s ^ 2) j 0 := by
  obtain ⟨K, hK, hψ⟩ := exists_sieveCutoff_bounded
  have hI := cutoffCubeIntegrand_integrable hG (sieveCutoff_sq_bounded hK hψ) j 0
  have hGi : Integrable G unitIntervalMeasure := hG.integrableOn_Icc
  have hprod := Integrable.fintype_prod (fun _ : Fin j => hGi)
  have hmoment := tensorCoordinateSum_integrable hG j
  have h := integral_mono_ae (hprod.sub (hmoment.const_mul (10 / 9))) hI (by
    filter_upwards [ae_unitCube j] with t ht
    have hs0 : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _hi => (ht i).1)
    have hp0 : 0 ≤ ∏ i, G (t i) := Finset.prod_nonneg (fun i _hi => hG0 _ (ht i))
    have hb := mul_le_mul_of_nonneg_left (sieveCutoff_sq_lower hs0) hp0
    change (∏ i, G (t i)) - (10 / 9) * ((∑ i, t i) * ∏ i, G (t i)) ≤
      (∏ i, G (t i)) * sieveCutoff (0 + ∑ i, t i) ^ 2
    rw [zero_add]
    nlinarith)
  simp only [Pi.sub_apply] at h
  rw [integral_sub hprod (hmoment.const_mul (10 / 9)), integral_const_mul,
    integral_tensorCoordinateSum hG j, integral_fintype_prod_eq_pow,
    unitIntervalMeasure_integral] at h
  simpa only [cutoffCubeIntegral, Fintype.card_fin, mul_assoc] using h

theorem cutoffCubeIntegral_sieveCutoff_sq_ge_third {G : ℝ → ℝ} (hG : Continuous G)
    (hG0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G t) (j : ℕ)
    (hsmall : (j : ℝ) * (∫ t in (0 : ℝ)..1, t * G t) ≤ (3 / 5) * (∫ t in (0 : ℝ)..1, G t)) :
    (∫ t in (0 : ℝ)..1, G t) ^ j / 3 ≤
      cutoffCubeIntegral G (fun s => sieveCutoff s ^ 2) j 0 := by
  cases j with
  | zero =>
      rw [cutoffCubeIntegral_zero]
      change (1 : ℝ) / 3 ≤ sieveCutoff 0 ^ 2
      rw [sieveCutoff_one_of_le (by norm_num : (0 : ℝ) ≤ 9 / 10)]
      norm_num
  | succ j =>
      have ha : 0 ≤ (∫ t in (0 : ℝ)..1, G t) :=
        intervalIntegral.integral_nonneg zero_le_one hG0
      have hscale := mul_le_mul_of_nonneg_right hsmall (pow_nonneg ha j)
      have hl := cutoffCubeIntegral_sieveCutoff_sq_lower hG hG0 (j + 1)
      simp only [Nat.add_sub_cancel, pow_succ] at hl ⊢
      nlinarith

theorem sieveProfile_energy_bounds {T U : ℝ} (hT : 0 < T) (hU : 0 < U) (hU1 : U ≤ 1) (j : ℕ)
    (hsmall : (j : ℝ) * (Real.log (1 + T * U) / T ^ 2) ≤
      (3 / 5) * (((9 / 10) * U) / (1 + T * ((9 / 10) * U)))) :
    (∫ t in (0 : ℝ)..1, sieveFactor T U t ^ 2) ^ j / 3 ≤
      cutoffCubeIntegral (fun t => sieveFactor T U t ^ 2) (fun s => sieveCutoff s ^ 2) j 0 ∧
    cutoffCubeIntegral (fun t => sieveFactor T U t ^ 2) (fun s => sieveCutoff s ^ 2) j 0 ≤
      (∫ t in (0 : ℝ)..1, sieveFactor T U t ^ 2) ^ j := by
  have hG : Continuous (fun t : ℝ => sieveFactor T U t ^ 2) :=
    (sieveFactor_contDiff T U (n := 1)).continuous.pow 2
  have hG0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ sieveFactor T U t ^ 2 := fun t _ht => sq_nonneg _
  have hmass : ((9 / 10) * U) / (1 + T * ((9 / 10) * U)) ≤
      ∫ t in (0 : ℝ)..1, sieveFactor T U t ^ 2 := by
    rw [sieveFactor_sq_unit_mass_eq hU hU1]
    exact sieveFactor_sq_mass_lower hT.le hU
  have hm : (j : ℝ) * (∫ t in (0 : ℝ)..1, t * sieveFactor T U t ^ 2) ≤
      (3 / 5) * (∫ t in (0 : ℝ)..1, sieveFactor T U t ^ 2) := by
    calc
      _ ≤ (j : ℝ) * (Real.log (1 + T * U) / T ^ 2) :=
        mul_le_mul_of_nonneg_left (sieveFactor_firstMoment_unit_bound hT hU hU1) (Nat.cast_nonneg j)
      _ ≤ _ := hsmall.trans (mul_le_mul_of_nonneg_left hmass (by norm_num))
  exact ⟨cutoffCubeIntegral_sieveCutoff_sq_ge_third hG hG0 j hm,
    cutoffCubeIntegral_sieveCutoff_sq_upper hG hG0 j⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.cutoffCubeIntegral_sieveCutoff_sq_ge_third
#print axioms Erdos4b.FGKMT.sieveProfile_energy_bounds
