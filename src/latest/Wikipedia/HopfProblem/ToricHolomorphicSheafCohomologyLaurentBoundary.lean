import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurentRadius
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegralKernels
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegralOperator

/-!
# Boundary data for the parameter-dependent Laurent projections

Holomorphic functions on `ℂ × ℂ*` restrict to genuine continuous functions
on each boundary torus. Inserting the actual Cauchy formula in the first
coordinate expresses a weighted second-coordinate contour integral as a
literal double contour integral with these fixed boundary data.
-/

noncomputable section

open Complex Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent

open HolomorphicCousin CuspNormalization.Germs.NormalIntegral

theorem circle_ne_zero {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ sphere 0 R) :
    w ≠ 0 := by
  intro he
  subst w
  have hzero : (0 : ℝ) = R := by simpa only [mem_sphere, dist_self] using hw
  exact hR.ne' hzero.symm

theorem firstSlice_analytic {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) {w : ℂ} (hw : w ≠ 0) :
    AnalyticOnNhd ℂ (fun z => f (z, w)) univ := by
  intro z _
  exact (hf (z, w) hw).curry_left

theorem secondSlice_analytic {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) (z : ℂ) :
    AnalyticOnNhd ℂ (fun w => f (z, w)) {w | w ≠ 0} := by
  intro w hw
  exact (hf (z, w) hw).curry_right

/-- The actual boundary values, with the second circle disjoint from the
deleted coordinate hyperplane. -/
def boundaryData {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) (r R : ℝ) (hR : 0 < R) :
    C(BoundaryTorus r R, ℂ) := by
  let e : BoundaryTorus r R → ℂ × ℂ := fun w => (w.1.1, w.2.1)
  have he : Continuous e :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  refine ⟨fun w => f (e w), hf.continuousOn.comp_continuous he ?_⟩
  intro w
  exact circle_ne_zero hR w.2.2

@[simp] theorem boundaryData_apply {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) (r R : ℝ) (hR : 0 < R)
    (w : BoundaryTorus r R) : boundaryData hf r R hR w = f (w.1.1, w.2.1) := rfl

theorem firstSlice_circleFormula {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) {w : ℂ} (hw : w ≠ 0)
    {r : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    (2 * Real.pi * I : ℂ)⁻¹ *
      (∮ ζ in C(0, r), (ζ - z)⁻¹ * f (ζ, w)) = f (z, w) := by
  have hd : Differentiable ℂ (fun v => f (v, w)) :=
    fun v => (firstSlice_analytic hf hw v (mem_univ _)).differentiableAt
  simpa only [smul_eq_mul] using
    hd.diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz

/-- A weighted second-coordinate contour is an actual double Cauchy
integral. The weight need not satisfy any regularity assumption. -/
theorem weighted_doubleCircleIntegral_eq {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) (k : ℂ → ℂ) :
    (2 * Real.pi * I : ℂ)⁻¹ ^ 2 *
      (∮ η in C(0, R), ∮ ζ in C(0, r), (ζ - z)⁻¹ * k η * f (ζ, η)) =
      (2 * Real.pi * I : ℂ)⁻¹ * (∮ η in C(0, R), k η * f (z, η)) := by
  have hinner (η : ℂ) (hη : η ∈ sphere (0 : ℂ) R) :
      (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ ζ in C(0, r), (ζ - z)⁻¹ * k η * f (ζ, η)) = k η * f (z, η) := by
    have hfirst := firstSlice_circleFormula hf (circle_ne_zero hR hη) hz
    have hfactor :
        (∮ ζ in C(0, r), (ζ - z)⁻¹ * k η * f (ζ, η)) =
          k η * (∮ ζ in C(0, r), (ζ - z)⁻¹ * f (ζ, η)) := by
      calc
        _ = ∮ ζ in C(0, r), k η * ((ζ - z)⁻¹ * f (ζ, η)) := by
          apply circleIntegral.integral_congr hr.le
          intro ζ _
          ring
        _ = _ := circleIntegral.integral_const_mul _ _ _ _
    rw [hfactor]
    calc
      _ = k η * ((2 * Real.pi * I : ℂ)⁻¹ *
          (∮ ζ in C(0, r), (ζ - z)⁻¹ * f (ζ, η))) := by ring
      _ = _ := by rw [hfirst]
  calc
    _ = (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ η in C(0, R), (2 * Real.pi * I : ℂ)⁻¹ *
          (∮ ζ in C(0, r), (ζ - z)⁻¹ * k η * f (ζ, η))) := by
      rw [circleIntegral.integral_const_mul]
      ring
    _ = _ := by
      congr 1
      exact circleIntegral.integral_congr hR.le hinner

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent
