import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# The derivative of a quadratic germ equivalence preserves its quadratic form

Along each line, divide the chart transition by its scalar parameter.
The derivative is the limit of these vectors. Quadratic homogeneity and
continuity pass the exact germ identity to that limit, giving a genuine
linear equivalence of quadratic forms when the derivative is invertible.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem quadratic_germ_derivative (Q : QuadraticForm ℝ A) (R : QuadraticForm ℝ B)
    (hR : Continuous R) {F : A → B} {L : A →L[ℝ] B}
    (hF : HasFDerivAt F L 0) (hF0 : F 0 = 0)
    (hquad : (fun x => R (F x)) =ᶠ[𝓝 0] Q) (v : A) : R (L v) = Q v := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hcurve : HasDerivAt (fun t : ℝ => F (t • v)) (L v) 0 :=
    hF.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • F (t • v)) (𝓝[≠] 0) (𝓝 (L v)) := by
    simpa only [zero_add, zero_smul, hF0, sub_zero] using hcurve.tendsto_slope_zero
  have hpath : Tendsto (fun t : ℝ => t • v) (𝓝[≠] 0) (𝓝 (0 : A)) := by
    have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
    simpa only [zero_smul] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have heq : (fun t : ℝ => R (t⁻¹ • F (t • v))) =ᶠ[𝓝[≠] 0] fun _ => Q v := by
    filter_upwards [hquad.comp_tendsto hpath, self_mem_nhdsWithin] with t ht hne
    have ht0 : t ≠ 0 := hne
    change R (F (t • v)) = Q (t • v) at ht
    rw [R.map_smul, ht, Q.map_smul]
    simp only [smul_eq_mul]
    field_simp
  exact tendsto_nhds_unique (hR.continuousAt.tendsto.comp hslope)
    ((tendsto_congr' heq).mpr tendsto_const_nhds)

theorem equivalent_quadratic_germs_of_bijective_derivative
    (Q : QuadraticForm ℝ A) (R : QuadraticForm ℝ B) (hR : Continuous R)
    {F : A → B} {L : A →L[ℝ] B} (hF : HasFDerivAt F L 0)
    (hF0 : F 0 = 0) (hL : Bijective L)
    (hquad : (fun x => R (F x)) =ᶠ[𝓝 0] Q) : Q.Equivalent R := by
  let e := LinearEquiv.ofBijective L.toLinearMap hL
  exact ⟨{ e with map_app' := quadratic_germ_derivative Q R hR hF hF0 hquad }⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
