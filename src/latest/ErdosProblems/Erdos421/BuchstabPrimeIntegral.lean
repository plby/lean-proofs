import ErdosProblems.Erdos421.BuchstabPrimeSplitting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # The exact change of variables in Buchstab prime summation -/

namespace Erdos421

open MeasureTheory

theorem logarithmicBuchstabArgument_sqrt {X : ℝ} (hX : 1 < X) :
    logarithmicBuchstabArgument X (Real.sqrt X) = 1 := by
  have hlog := Real.log_pos hX
  rw [logarithmicBuchstabArgument, Real.log_sqrt (by linarith : 0 ≤ X)]
  field_simp
  norm_num

theorem buchstabPrimeWeight_integral {F : ℝ → ℝ} (hF : Continuous F)
    {X a b : ℝ} (hX : 1 < X) (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, buchstabPrimeWeight X F t) =
      (∫ u in logarithmicBuchstabArgument X b..logarithmicBuchstabArgument X a, F u) /
        Real.log X := by
  have hsub : Set.uIcc a b ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hab]
    exact fun _ ht ↦ ha.trans_le ht.1
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (logarithmicBuchstabArgument X)
      (-Real.log X / (t * (Real.log t) ^ 2)) t :=
    fun t ht ↦ logarithmicBuchstabArgument_hasDerivAt X (hsub ht)
  have hc : ContinuousOn (fun t : ℝ ↦ -Real.log X / (t * (Real.log t) ^ 2))
      (Set.uIcc a b) := by
    convert (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ -Real.log X) (Set.uIcc a b)).mul
      (reciprocalLogSquare_continuousOn.mono hsub) using 1
    funext t
    dsimp only [reciprocalLogSquare, Pi.mul_apply]
    ring
  have hs := intervalIntegral.integral_comp_mul_deriv hd hc hF
  have heq : (∫ t in a..b,
      F (logarithmicBuchstabArgument X t) * (-Real.log X / (t * (Real.log t) ^ 2))) =
      -Real.log X * ∫ t in a..b, buchstabPrimeWeight X F t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [buchstabPrimeWeight, reciprocalLogSquare]
    ring
  dsimp only [Function.comp_apply] at hs
  rw [heq] at hs
  have hflip := intervalIntegral.integral_symm (f := F) (μ := volume)
    (logarithmicBuchstabArgument X b) (logarithmicBuchstabArgument X a)
  apply (eq_div_iff (Real.log_pos hX).ne').mpr
  linarith only [hs, hflip]

theorem buchstabPrimeWeight_main_term (n : ℕ) {X z : ℝ}
    (hX : 1 < X) (hz : 1 < z) (hzX : z ≤ Real.sqrt X) :
    1 / Real.log X + (∫ t in z..Real.sqrt X, buchstabPrimeWeight X (finiteBuchstab n) t) =
      finiteBuchstab (n + 1) (Real.log X / Real.log z) / Real.log z := by
  have hsqrt : 1 < Real.sqrt X := hz.trans_le hzX
  have harg := logarithmicBuchstabArgument_antitone hX hz hsqrt hzX
  rw [logarithmicBuchstabArgument_sqrt hX] at harg
  have hs : 2 ≤ Real.log X / Real.log z := by
    dsimp only [logarithmicBuchstabArgument] at harg
    linarith
  rw [buchstabPrimeWeight_integral (finiteBuchstab_continuous n) hX hz hzX,
    logarithmicBuchstabArgument_sqrt hX, finiteBuchstab_step n hs,
    intervalIntegral.integral_comp_sub_right (finiteBuchstab n) 1]
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num]
  dsimp only [logarithmicBuchstabArgument]
  have hlogX := Real.log_pos hX
  have hlogz := Real.log_pos hz
  field_simp

end Erdos421
