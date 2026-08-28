import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegral

/-!
# A genuine joint analytic unit from analytic slice factors

The unit is the existing fixed-circle Cauchy quotient, not a choice of the
slice factors. Boundary cancellation and the ordinary Cauchy formula show
that this explicit joint function agrees with every supplied analytic
slice factor inside the second disc. The denominator may vanish there.
-/

noncomputable section

open Set Metric Filter Topology
open Wikipedia.HopfProblem.CuspNormalization.Germs

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.PreparationUnit

/-- The actual quotient integral equals an analytic slice factor inside
the disc. Only the integration circle must avoid the denominator's zeros. -/
theorem cauchyQuotient_eq_slice_factor {f P : ℂ × ℂ → ℂ} {g : ℂ → ℂ}
    {R : ℝ} {z w : ℂ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hP₀ : ∀ ζ ∈ sphere 0 R, P (z, ζ) ≠ 0)
    (hfg : EqOn (fun ζ ↦ f (z, ζ)) (fun ζ ↦ P (z, ζ) * g ζ) (closedBall 0 R))
    (hw : w ∈ ball 0 R) :
    NormalIntegral.cauchyQuotient f P R (z, w) = g w := by
  have hdc : DiffContOnCl ℂ g (ball 0 R) :=
    (hg.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  have hboundary : EqOn
      (fun ζ ↦ (ζ - w)⁻¹ * (f (z, ζ) / P (z, ζ)))
      (fun ζ ↦ (ζ - w)⁻¹ * g ζ) (sphere 0 R) := by
    intro ζ hζ
    dsimp only
    have hfζ : f (z, ζ) = P (z, ζ) * g ζ := hfg (sphere_subset_closedBall hζ)
    rw [hfζ]
    simp [hP₀ ζ hζ]
  calc
    NormalIntegral.cauchyQuotient f P R (z, w) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ ζ in C(0, R), (ζ - w)⁻¹ * g ζ := by
      unfold NormalIntegral.cauchyQuotient
      congr 1
      exact circleIntegral.integral_congr hR.le hboundary
    _ = g w := by
      simpa only [smul_eq_mul] using
        hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

/-- Analytic slice units give an explicit jointly analytic, nonvanishing
unit and an actual factorization everywhere on the open bidisc. -/
theorem cauchyQuotient_unit_on_bidisc {f P : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hP : AnalyticOnNhd ℂ P (closedBall 0 r ×ˢ closedBall 0 R))
    (hP₀ : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, P p ≠ 0)
    (hslices : ∀ z ∈ closedBall (0 : ℂ) r,
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
        (∀ w ∈ closedBall 0 R, g w ≠ 0) ∧
        EqOn (fun w ↦ f (z, w)) (fun w ↦ P (z, w) * g w) (closedBall 0 R)) :
    AnalyticOnNhd ℂ (NormalIntegral.cauchyQuotient f P R) (ball 0 r ×ˢ ball 0 R) ∧
      EqOn f (fun p ↦ P p * NormalIntegral.cauchyQuotient f P R p)
        (ball 0 r ×ˢ ball 0 R) ∧
      (∀ p ∈ ball 0 r ×ˢ ball 0 R, NormalIntegral.cauchyQuotient f P R p ≠ 0) := by
  have hpoint (p : ℂ × ℂ) (hp : p ∈ ball 0 r ×ˢ ball 0 R) :
      f p = P p * NormalIntegral.cauchyQuotient f P R p ∧
        NormalIntegral.cauchyQuotient f P R p ≠ 0 := by
    obtain ⟨g, hg, hg₀, hfg⟩ := hslices p.1 (ball_subset_closedBall hp.1)
    have hu : NormalIntegral.cauchyQuotient f P R p = g p.2 :=
      cauchyQuotient_eq_slice_factor hR hg
        (fun ζ hζ ↦ hP₀ (p.1, ζ) ⟨ball_subset_closedBall hp.1, hζ⟩) hfg hp.2
    rw [hu]
    exact ⟨hfg (ball_subset_closedBall hp.2), hg₀ p.2 (ball_subset_closedBall hp.2)⟩
  refine ⟨NormalIntegral.cauchyQuotient_analyticOnNhd hr hR hf hP hP₀, ?_, ?_⟩
  · intro p hp
    exact (hpoint p hp).1
  · intro p hp
    exact (hpoint p hp).2

/-- The same explicit Cauchy quotient is a genuine analytic unit germ at
the origin, with the supplied function equal to `P` times that germ. -/
theorem cauchyQuotient_unit_germ {f P : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hP : AnalyticOnNhd ℂ P (closedBall 0 r ×ˢ closedBall 0 R))
    (hP₀ : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, P p ≠ 0)
    (hslices : ∀ z ∈ closedBall (0 : ℂ) r,
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
        (∀ w ∈ closedBall 0 R, g w ≠ 0) ∧
        EqOn (fun w ↦ f (z, w)) (fun w ↦ P (z, w) * g w) (closedBall 0 R)) :
    AnalyticAt ℂ (NormalIntegral.cauchyQuotient f P R) 0 ∧
      NormalIntegral.cauchyQuotient f P R 0 ≠ 0 ∧
      f =ᶠ[𝓝 (0 : ℂ × ℂ)] (fun p ↦ P p * NormalIntegral.cauchyQuotient f P R p) := by
  obtain ⟨hu, hfu, hu₀⟩ := cauchyQuotient_unit_on_bidisc hr hR hf hP hP₀ hslices
  have hzero : (0 : ℂ × ℂ) ∈ ball 0 r ×ˢ ball 0 R :=
    ⟨mem_ball_self hr, mem_ball_self hR⟩
  refine ⟨hu 0 hzero, hu₀ 0 hzero, ?_⟩
  filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds hzero] with p hp
  exact hfu hp

end Wikipedia.HopfProblem.AnalyticGermsFactorial.PreparationUnit
