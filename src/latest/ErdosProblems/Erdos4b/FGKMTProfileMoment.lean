/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTProfileCost
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# First mass and first moment of the explicit sieve factor

The logarithmic estimates are exact inequalities in the two parameters.
They are used to prove the face-energy amplification and to bound the
mass removed by the cutoff on the sum of coordinates.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory Filter

theorem rationalProfile_continuousOn {T b : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => 1 / (1 + T * t)) (Set.Icc 0 b) := by
  apply continuousOn_const.div
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  change 1 + T * t ≠ 0
  positivity

theorem integral_rationalProfile {T b : ℝ} (hT : 0 < T) (hb : 0 ≤ b) :
    (∫ t in (0 : ℝ)..b, 1 / (1 + T * t)) = Real.log (1 + T * b) / T := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) b,
      HasDerivAt (fun t : ℝ => Real.log (1 + T * t) / T) (1 / (1 + T * t)) t := by
    intro t ht
    have ht0 : 0 ≤ t := (Set.uIcc_of_le hb ▸ ht).1
    have hden : 1 + T * t ≠ 0 := ne_of_gt (by positivity)
    convert! ((((hasDerivAt_id t).const_mul T).const_add 1).log hden).div_const T using 1
    simp only [id_eq, mul_one]
    field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((rationalProfile_continuousOn hT.le).intervalIntegrable_of_Icc hb)
  simpa only [mul_zero, add_zero, Real.log_one, zero_div, sub_zero] using h

theorem sieveFactor_mass_bounds {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    Real.log (1 + T * ((9 / 10) * U)) / T ≤ (∫ t in (0 : ℝ)..U, sieveFactor T U t) ∧
      (∫ t in (0 : ℝ)..U, sieveFactor T U t) ≤ Real.log (1 + T * U) / T := by
  have hb : 0 ≤ (9 / 10 : ℝ) * U := by positivity
  have hc := (sieveFactor_contDiff T U (n := 1)).continuous
  constructor
  · calc
      _ = ∫ t in (0 : ℝ)..((9 / 10) * U), 1 / (1 + T * t) :=
        (integral_rationalProfile hT hb).symm
      _ = ∫ t in (0 : ℝ)..((9 / 10) * U), sieveFactor T U t :=
        intervalIntegral.integral_congr (by
          intro t ht
          have ht' : t ∈ Set.Icc (0 : ℝ) ((9 / 10) * U) := Set.uIcc_of_le hb ▸ ht
          exact (sieveFactor_eq_inv hT.le hU ht'.1 ht'.2).symm)
      _ ≤ ∫ t in (0 : ℝ)..U, sieveFactor T U t :=
        intervalIntegral.integral_mono_interval le_rfl hb (by linarith)
          (Eventually.of_forall (sieveFactor_nonneg T U)) (hc.intervalIntegrable 0 U)
  · rw [← integral_rationalProfile hT hU.le]
    exact intervalIntegral.integral_mono_on hU.le (hc.intervalIntegrable 0 U)
      ((rationalProfile_continuousOn hT.le).intervalIntegrable_of_Icc hU.le)
      (fun t ht => sieveFactor_le_inv hT.le ht.1 U)

theorem sieveFactor_firstMoment_bound {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    (∫ t in (0 : ℝ)..U, t * sieveFactor T U t ^ 2) ≤ Real.log (1 + T * U) / T ^ 2 := by
  have hc := continuous_id.mul ((sieveFactor_contDiff T U (n := 1)).continuous.pow 2)
  have hrat : ContinuousOn (fun t : ℝ => (1 / T) * (1 / (1 + T * t))) (Set.Icc 0 U) :=
    continuousOn_const.mul (rationalProfile_continuousOn (b := U) hT.le)
  calc
    _ ≤ ∫ t in (0 : ℝ)..U, (1 / T) * (1 / (1 + T * t)) :=
      intervalIntegral.integral_mono_on hU.le (hc.intervalIntegrable 0 U)
        (hrat.intervalIntegrable_of_Icc hU.le) (by
          intro t ht
          have ht0 : 0 ≤ t := ht.1
          have hden : 0 < 1 + T * t := by positivity
          have hsq := pow_le_pow_left₀ (sieveFactor_nonneg T U t)
            (sieveFactor_le_inv hT.le ht0 U) 2
          have hfrac : t / (1 + T * t) ≤ 1 / T :=
            (div_le_div_iff₀ hden hT).mpr (by nlinarith)
          calc
            _ ≤ t * (1 / (1 + T * t)) ^ 2 := mul_le_mul_of_nonneg_left hsq ht0
            _ = (t / (1 + T * t)) * (1 / (1 + T * t)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hfrac (by positivity))
    _ = (1 / T) * (Real.log (1 + T * U) / T) := by
      rw [intervalIntegral.integral_const_mul, integral_rationalProfile hT hU.le]
    _ = _ := by ring

theorem sieveFactor_firstMoment_unit_eq {U : ℝ} (hU : 0 < U) (hU1 : U ≤ 1) (T : ℝ) :
    (∫ t in (0 : ℝ)..1, t * sieveFactor T U t ^ 2) =
      ∫ t in (0 : ℝ)..U, t * sieveFactor T U t ^ 2 := by
  have hc : Continuous (fun t : ℝ => t * sieveFactor T U t ^ 2) :=
    continuous_id.mul ((sieveFactor_contDiff T U (n := 1)).continuous.pow 2)
  have htail : (∫ t in U..1, t * sieveFactor T U t ^ 2) = 0 := by
    calc
      _ = ∫ _t in U..1, (0 : ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        have htU : U ≤ t := (Set.uIcc_of_le hU1 ▸ ht).1
        change t * sieveFactor T U t ^ 2 = 0
        rw [sieveFactor_zero_of_ge hU htU T, zero_pow (by norm_num), mul_zero])
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 U)
    (hc.intervalIntegrable U 1), htail, add_zero]

theorem sieveFactor_firstMoment_unit_bound {T U : ℝ} (hT : 0 < T) (hU : 0 < U) (hU1 : U ≤ 1) :
    (∫ t in (0 : ℝ)..1, t * sieveFactor T U t ^ 2) ≤ Real.log (1 + T * U) / T ^ 2 := by
  rw [sieveFactor_firstMoment_unit_eq hU hU1]
  exact sieveFactor_firstMoment_bound hT hU

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveFactor_mass_bounds
#print axioms Erdos4b.FGKMT.sieveFactor_firstMoment_unit_bound
