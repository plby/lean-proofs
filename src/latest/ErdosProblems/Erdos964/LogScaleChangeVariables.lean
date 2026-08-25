import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic rescaling on a positive interval
-/

namespace Erdos964

open MeasureTheory

theorem logScale_mem (L x y t : ℝ) (hL : 0 < L) (hx : 0 < x)
    (ht : t ∈ Set.Icc x y) :
    Real.log t / L ∈ Set.Icc (Real.log x / L) (Real.log y / L) := by
  exact ⟨div_le_div_of_nonneg_right (Real.log_le_log hx ht.1) hL.le,
    div_le_div_of_nonneg_right (Real.log_le_log (hx.trans_le ht.1) ht.2) hL.le⟩

theorem hasDerivAt_logScale (L t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun u => Real.log u / L) (1 / (L * t)) t := by
  exact ((Real.hasDerivAt_log ht).div_const L).congr_deriv (by
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul])

theorem integral_logScale (L x y : ℝ) (hL : 0 < L) (hx : 0 < x) (hxy : x ≤ y)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc (Real.log x / L) (Real.log y / L))) :
    (∫ t in x..y, g (Real.log t / L) / (L * t)) =
      ∫ u in (Real.log x / L)..(Real.log y / L), g u := by
  have hderiv : ∀ t ∈ Set.uIcc x y,
      HasDerivAt (fun u => Real.log u / L) (1 / (L * t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    exact hasDerivAt_logScale L t (hx.trans_le ht.1).ne'
  have hcont : ContinuousOn (fun t => 1 / (L * t)) (Set.uIcc x y) := by
    apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    exact mul_ne_zero hL.ne' (hx.trans_le ht.1).ne'
  have hgimage : ContinuousOn g ((fun t => Real.log t / L) '' Set.uIcc x y) := by
    apply hg.mono
    rintro z ⟨t, ht, rfl⟩
    exact logScale_mem L x y t hL hx (by simpa only [Set.uIcc_of_le hxy] using ht)
  have h := intervalIntegral.integral_comp_mul_deriv' hderiv hcont hgimage
  simpa only [Function.comp_apply, mul_one_div] using h

noncomputable def logScaleTest (L : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  g (Real.log t / L) / L

theorem hasDerivAt_logScaleTest (L t : ℝ) (ht : t ≠ 0)
    (g : ℝ → ℝ) (hg : DifferentiableAt ℝ g (Real.log t / L)) :
    HasDerivAt (logScaleTest L g) (deriv g (Real.log t / L) / (L ^ 2 * t)) t := by
  have h := ((hg.hasDerivAt.comp t (hasDerivAt_logScale L t ht)).div_const L).congr_deriv
    (show deriv g (Real.log t / L) * (1 / (L * t)) / L =
        deriv g (Real.log t / L) / (L ^ 2 * t) by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring)
  exact h

theorem continuousOn_logScaleTest_deriv (L x y : ℝ) (hL : 0 < L) (hx : 0 < x)
    (g : ℝ → ℝ)
    (hg : ∀ z ∈ Set.Icc (Real.log x / L) (Real.log y / L), DifferentiableAt ℝ g z)
    (hg' : ContinuousOn (deriv g) (Set.Icc (Real.log x / L) (Real.log y / L))) :
    ContinuousOn (deriv (logScaleTest L g)) (Set.Icc x y) := by
  have hmap : ContinuousOn (fun t => Real.log t / L) (Set.Icc x y) :=
    (Real.continuousOn_log.mono (fun t ht => (hx.trans_le ht.1).ne')).div_const L
  have hcomp := hg'.comp hmap (fun t ht => logScale_mem L x y t hL hx ht)
  have hd : ContinuousOn (fun t => deriv g (Real.log t / L) / (L ^ 2 * t))
      (Set.Icc x y) := hcomp.div (continuousOn_const.mul continuousOn_id)
        (fun t ht => mul_ne_zero (pow_ne_zero _ hL.ne') (hx.trans_le ht.1).ne')
  apply hd.congr
  intro t ht
  exact (hasDerivAt_logScaleTest L t (hx.trans_le ht.1).ne' g
    (hg _ (logScale_mem L x y t hL hx ht))).deriv

theorem integral_abs_deriv_logScaleTest (L x y : ℝ) (hL : 0 < L) (hx : 0 < x)
    (hxy : x ≤ y) (g : ℝ → ℝ)
    (hg : ∀ z ∈ Set.Icc (Real.log x / L) (Real.log y / L), DifferentiableAt ℝ g z)
    (hg' : ContinuousOn (deriv g) (Set.Icc (Real.log x / L) (Real.log y / L))) :
    (∫ t in x..y, |deriv (logScaleTest L g) t|) =
      (∫ z in (Real.log x / L)..(Real.log y / L), |deriv g z|) / L := by
  calc
    _ = ∫ t in x..y, |deriv g (Real.log t / L)| / (L * t) / L := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hxy] at ht
      have htpos := hx.trans_le ht.1
      dsimp only
      rw [(hasDerivAt_logScaleTest L t htpos.ne' g
        (hg _ (logScale_mem L x y t hL hx ht))).deriv,
        abs_div, abs_of_pos (mul_pos (pow_pos hL 2) htpos)]
      ring
    _ = (∫ t in x..y, |deriv g (Real.log t / L)| / (L * t)) / L :=
      intervalIntegral.integral_div _ _
    _ = _ := by rw [integral_logScale L x y hL hx hxy (fun z => |deriv g z|) hg'.abs]

end Erdos964
