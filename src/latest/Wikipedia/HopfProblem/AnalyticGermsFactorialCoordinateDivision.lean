import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegral

/-!
# Analytic division by a coordinate

Subtracting two one-variable Cauchy formulas identifies the quotient by the
second coordinate with an actual fixed-circle integral.  The existing
joint-analyticity theorem for that integral supplies an analytic quotient
on a bidisc.  Swapping coordinates gives division by the first coordinate.
No formal power-series model or preparation theorem is used.
-/

open Set Metric Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.CoordinateDivision

/-- The fixed-circle quotient by the second coordinate computes the
difference from the value on the first coordinate axis. -/
theorem snd_mul_cauchyQuotient_eq_sub {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    {z : ℂ × ℂ} (hz : z ∈ ball 0 r ×ˢ ball 0 R) :
    z.2 * NormalIntegral.cauchyQuotient f Prod.snd R z = f z - f (z.1, 0) := by
  have hslice : AnalyticOnNhd ℂ (fun w : ℂ => f (z.1, w)) (closedBall 0 R) := by
    intro w hw
    exact (hf (z.1, w) ⟨ball_subset_closedBall hz.1, hw⟩).comp₂
      analyticAt_const analyticAt_id
  have hdc : DiffContOnCl ℂ (fun w : ℂ => f (z.1, w)) (ball 0 R) :=
    (hslice.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  have hformula : (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (∮ w in C(0, R), (w - z.2)⁻¹ * f (z.1, w)) = f z := by
    simpa only [smul_eq_mul] using
      hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz.2
  have hformula0 : (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (∮ w in C(0, R), w⁻¹ * f (z.1, w)) = f (z.1, 0) := by
    simpa only [smul_eq_mul, sub_zero] using
      hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (mem_ball_self hR)
  have hne (w : ℂ) (hw : w ∈ sphere (0 : ℂ) R) : w - z.2 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_mem_of_not_mem hw (ne_of_lt hz.2))
  have hne0 (w : ℂ) (hw : w ∈ sphere (0 : ℂ) R) : w ≠ 0 :=
    ne_of_mem_sphere hw hR.ne'
  have hc : ContinuousOn (fun w : ℂ => f (z.1, w)) (sphere 0 R) :=
    hslice.continuousOn.mono sphere_subset_closedBall
  have hi : CircleIntegrable (fun w : ℂ => (w - z.2)⁻¹ * f (z.1, w)) 0 R :=
    (((continuousOn_id.sub continuousOn_const).inv₀ hne).mul hc).circleIntegrable hR.le
  have hi0 : CircleIntegrable (fun w : ℂ => w⁻¹ * f (z.1, w)) 0 R :=
    ((continuousOn_id.inv₀ hne0).mul hc).circleIntegrable hR.le
  calc
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ w in C(0, R), z.2 * ((w - z.2)⁻¹ * (f (z.1, w) / w))) := by
      simp only [NormalIntegral.cauchyQuotient, circleIntegral.integral_const_mul]
      ring
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ w in C(0, R), (w - z.2)⁻¹ * f (z.1, w) - w⁻¹ * f (z.1, w)) := by
      congr 1
      apply circleIntegral.integral_congr hR.le
      intro w hw
      field_simp [hne w hw, hne0 w hw]
      ring
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ w in C(0, R), (w - z.2)⁻¹ * f (z.1, w)) -
        (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ w in C(0, R), w⁻¹ * f (z.1, w)) := by
      rw [circleIntegral.integral_sub hi hi0, mul_sub]
    _ = _ := by rw [hformula, hformula0]

/-- A local analytic function differs from its restriction to the first
axis by the second coordinate times another actual analytic function. -/
theorem exists_analytic_sub_axis_mul_snd {f : ℂ × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) :
    ∃ g : ℂ × ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      (fun p => f p - f (p.1, 0)) =ᶠ[𝓝 (0 : ℂ × ℂ)] (fun p => p.2 * g p) := by
  obtain ⟨r, hr, hlocal⟩ := nhds_basis_closedBall.mem_iff.mp hf.eventually_analyticAt
  have hfdisc : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 r) := by
    intro p hp
    apply hlocal
    rw [← closedBall_prod_same]
    exact hp
  have hsnd : AnalyticOnNhd ℂ (Prod.snd : ℂ × ℂ → ℂ)
      (closedBall 0 r ×ˢ closedBall 0 r) := fun _ _ => analyticAt_snd
  have hboundary : ∀ p ∈ closedBall (0 : ℂ) r ×ˢ sphere (0 : ℂ) r, p.2 ≠ 0 :=
    fun p hp => ne_of_mem_sphere hp.2 hr.ne'
  refine ⟨NormalIntegral.cauchyQuotient f Prod.snd r,
    NormalIntegral.cauchyQuotient_analyticAt_zero hr hr hfdisc hsnd hboundary, ?_⟩
  have hnhds : ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ × ℂ) :=
    (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr, mem_ball_self hr⟩
  filter_upwards [hnhds] with p hp
  exact (snd_mul_cauchyQuotient_eq_sub hr hfdisc hp).symm

/-- An analytic function vanishing on the first axis is analytically
divisible by the second coordinate near the origin. -/
theorem exists_analytic_mul_snd {f : ℂ × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hzero : (fun w : ℂ => f (w, 0)) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∃ g : ℂ × ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      f =ᶠ[𝓝 (0 : ℂ × ℂ)] (fun p => p.2 * g p) := by
  obtain ⟨g, hg, hfg⟩ := exists_analytic_sub_axis_mul_snd hf
  refine ⟨g, hg, ?_⟩
  have hzero' : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), f (p.1, 0) = 0 :=
    (continuous_fst.tendsto (0 : ℂ × ℂ)).eventually hzero
  filter_upwards [hfg, hzero'] with p hp hp0
  simpa only [hp0, sub_zero] using hp

/-- Hadamard division in the first coordinate for actual analytic functions. -/
theorem exists_analytic_mul_fst {f : ℂ × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hzero : (fun w : ℂ => f (0, w)) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∃ g : ℂ × ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      f =ᶠ[𝓝 (0 : ℂ × ℂ)] (fun p => p.1 * g p) := by
  have hswap : AnalyticAt ℂ (Prod.swap : ℂ × ℂ → ℂ × ℂ) 0 :=
    analyticAt_snd.prod analyticAt_fst
  have hf' : AnalyticAt ℂ (fun p : ℂ × ℂ => f p.swap) 0 :=
    hf.comp_of_eq hswap rfl
  obtain ⟨g, hg, hfg⟩ := exists_analytic_mul_snd hf' hzero
  refine ⟨fun p => g p.swap, hg.comp_of_eq hswap rfl, ?_⟩
  have h := hfg.comp_tendsto (continuous_swap.tendsto (0 : ℂ × ℂ))
  filter_upwards [h] with p hp
  exact hp

end Wikipedia.HopfProblem.CuspNormalization.Germs.CoordinateDivision
