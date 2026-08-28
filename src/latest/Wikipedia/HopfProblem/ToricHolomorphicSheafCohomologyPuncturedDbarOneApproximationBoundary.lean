import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurentParametric

/-!
# The local parameter-disc Cauchy formula for Laurent approximation

Only a closed parameter disc times the integration circle is required in
the analytic hypothesis. This permits the actual contour construction for
functions defined on a finite disc–annulus region.
-/

noncomputable section

open Complex Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne

open CuspNormalization.Germs.NormalIntegral

def circleBoundaryData {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hf : ContinuousOn f (closedBall (0 : ℂ) r ×ˢ sphere 0 R)) :
    C(BoundaryTorus r R, ℂ) := by
  let e : BoundaryTorus r R → ℂ × ℂ := fun w => (w.1.1, w.2.1)
  have he : Continuous e :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  refine ⟨fun w => f (e w), hf.comp_continuous he ?_⟩
  intro w
  exact ⟨sphere_subset_closedBall w.1.2, w.2.2⟩

@[simp] theorem circleBoundaryData_apply {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hf : ContinuousOn f (closedBall (0 : ℂ) r ×ˢ sphere 0 R))
    (w : BoundaryTorus r R) : circleBoundaryData hf w = f (w.1.1, w.2.1) := rfl

theorem firstCircleFormula {f : ℂ × ℂ → ℂ} {r R : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r ×ˢ sphere 0 R))
    {w : ℂ} (hw : w ∈ sphere (0 : ℂ) R) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    (2 * Real.pi * I : ℂ)⁻¹ *
      (∮ ζ in C(0, r), (ζ - z)⁻¹ * f (ζ, w)) = f (z, w) := by
  have hd : DiffContOnCl ℂ (fun v => f (v, w)) (ball (0 : ℂ) r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) hr.ne']
    intro v hv
    exact (hf (v, w) ⟨hv, hw⟩).curry_left.differentiableAt.differentiableWithinAt
  simpa only [smul_eq_mul] using hd.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz

theorem weightedDoubleCircleIntegral_eq {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r ×ˢ sphere 0 R))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) (k : ℂ → ℂ) :
    (2 * Real.pi * I : ℂ)⁻¹ ^ 2 *
      (∮ η in C(0, R), ∮ ζ in C(0, r), (ζ - z)⁻¹ * k η * f (ζ, η)) =
      (2 * Real.pi * I : ℂ)⁻¹ * (∮ η in C(0, R), k η * f (z, η)) := by
  have hinner (η : ℂ) (hη : η ∈ sphere (0 : ℂ) R) :
      (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ ζ in C(0, r), (ζ - z)⁻¹ * k η * f (ζ, η)) = k η * f (z, η) := by
    have hfirst := firstCircleFormula hr hf hη hz
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

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne
