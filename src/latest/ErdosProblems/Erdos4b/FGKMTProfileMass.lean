/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSieveFactor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Explicit one-dimensional profile mass bounds

The rational comparison is integrated exactly. These estimates preserve
the leading constant in the square mass, as needed by the later Markov
bound for the sum of coordinates.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory Filter

theorem rationalProfile_sq_continuousOn {T b : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => (1 / (1 + T * t)) ^ 2) (Set.Icc 0 b) := by
  apply (continuousOn_const.div
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) ?_).pow 2
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  change 1 + T * t ≠ 0
  positivity

theorem integral_rationalProfile_sq {T b : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ b) :
    (∫ t in (0 : ℝ)..b, (1 / (1 + T * t)) ^ 2) = b / (1 + T * b) := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) b,
      HasDerivAt (fun t : ℝ => t / (1 + T * t)) ((1 / (1 + T * t)) ^ 2) t := by
    intro t ht
    have ht0 : 0 ≤ t := (Set.uIcc_of_le hb ▸ ht).1
    have hden : 1 + T * t ≠ 0 := ne_of_gt (by positivity)
    convert! (hasDerivAt_id t).fun_div
      (((hasDerivAt_id t).const_mul T).const_add 1) hden using 1
    simp only [id_eq, mul_one, one_mul]
    field_simp [hden]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((rationalProfile_sq_continuousOn hT).intervalIntegrable_of_Icc hb)
  simpa only [mul_zero, add_zero, zero_div, sub_zero] using h

theorem sieveFactor_pow_integral_eq {U L : ℝ} (hU : 0 < U) (hUL : U ≤ L)
    (T : ℝ) (m : ℕ) :
    (∫ t in (0 : ℝ)..L, sieveFactor T U t ^ (m + 1)) =
      ∫ t in (0 : ℝ)..U, sieveFactor T U t ^ (m + 1) := by
  have hc : Continuous (fun t : ℝ => sieveFactor T U t ^ (m + 1)) :=
    (sieveFactor_contDiff T U (n := 1)).continuous.pow _
  have htail : (∫ t in U..L, sieveFactor T U t ^ (m + 1)) = 0 := by
    calc
      _ = ∫ _t in U..L, (0 : ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        have htU : U ≤ t := (Set.uIcc_of_le hUL ▸ ht).1
        change sieveFactor T U t ^ (m + 1) = 0
        rw [sieveFactor_zero_of_ge hU htU T, zero_pow (by omega)])
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 U)
    (hc.intervalIntegrable U L), htail, add_zero]

theorem sieveFactor_sq_mass_lower {T U : ℝ} (hT : 0 ≤ T) (hU : 0 < U) :
    ((9 / 10) * U) / (1 + T * ((9 / 10) * U)) ≤
      ∫ t in (0 : ℝ)..U, sieveFactor T U t ^ 2 := by
  have hb : 0 ≤ (9 / 10 : ℝ) * U := by positivity
  have hc := (sieveFactor_contDiff T U (n := 1)).continuous.pow 2
  calc
    _ = ∫ t in (0 : ℝ)..((9 / 10) * U), (1 / (1 + T * t)) ^ 2 :=
      (integral_rationalProfile_sq hT hb).symm
    _ = ∫ t in (0 : ℝ)..((9 / 10) * U), sieveFactor T U t ^ 2 :=
      intervalIntegral.integral_congr (by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) ((9 / 10) * U) := Set.uIcc_of_le hb ▸ ht
        change (1 / (1 + T * t)) ^ 2 = sieveFactor T U t ^ 2
        rw [sieveFactor_eq_inv hT hU ht'.1 ht'.2])
    _ ≤ ∫ t in (0 : ℝ)..U, sieveFactor T U t ^ 2 :=
      intervalIntegral.integral_mono_interval le_rfl hb (by linarith)
        (Eventually.of_forall (fun t => sq_nonneg _)) (hc.intervalIntegrable 0 U)

theorem sieveFactor_sq_mass_upper {T U : ℝ} (hT : 0 ≤ T) (hU : 0 < U) :
    (∫ t in (0 : ℝ)..U, sieveFactor T U t ^ 2) ≤ U / (1 + T * U) := by
  rw [← integral_rationalProfile_sq hT hU.le]
  apply intervalIntegral.integral_mono_on hU.le
    (((sieveFactor_contDiff T U (n := 1)).continuous.pow 2).intervalIntegrable 0 U)
    ((rationalProfile_sq_continuousOn hT).intervalIntegrable_of_Icc hU.le)
  intro t ht
  exact pow_le_pow_left₀ (sieveFactor_nonneg T U t) (sieveFactor_le_inv hT ht.1 U) 2

theorem sieveFactor_sq_mass_le_inv {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    (∫ t in (0 : ℝ)..U, sieveFactor T U t ^ 2) ≤ 1 / T := by
  refine (sieveFactor_sq_mass_upper hT.le hU).trans ?_
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + T * U) hT).mpr
  nlinarith

theorem sieveFactor_sq_mass_pos {T U : ℝ} (hT : 0 ≤ T) (hU : 0 < U) :
    0 < (∫ t in (0 : ℝ)..U, sieveFactor T U t ^ 2) :=
  lt_of_lt_of_le (by positivity) (sieveFactor_sq_mass_lower hT hU)

theorem sieveFactor_sq_mass_ge_half_inv {T U : ℝ} (hT : 0 < T) (hU : 0 < U)
    (hTU : 2 ≤ T * U) :
    1 / (2 * T) ≤ ∫ t in (0 : ℝ)..U, sieveFactor T U t ^ 2 := by
  refine le_trans ?_ (sieveFactor_sq_mass_lower hT.le hU)
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * T) (by positivity)).mpr
  nlinarith

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveFactor_sq_mass_lower
#print axioms Erdos4b.FGKMT.sieveFactor_sq_mass_upper
#print axioms Erdos4b.FGKMT.sieveFactor_sq_mass_ge_half_inv
