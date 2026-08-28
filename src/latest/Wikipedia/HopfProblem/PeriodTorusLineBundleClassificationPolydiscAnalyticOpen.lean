import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticBasic

/-!
# Joint analyticity on arbitrary open subsets of two complex variables

An actual closed bidisc inside the open set supplies the two contour
integrals.  Translations preserve the coordinate-slice hypotheses, so the
bidisc result applies locally at every point.  The input is only joint
continuity and complex differentiability of each one-variable slice.
-/

noncomputable section

open Set Metric Filter Topology

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic

/-- A continuous, separately holomorphic scalar function on an open subset
of `ℂ × ℂ` is jointly analytic.  Each slice uses its actual open preimage. -/
theorem analyticOnNhd_of_continuousOn_of_slices {f : ℂ × ℂ → ℂ} {s : Set (ℂ × ℂ)}
    (hs : IsOpen s) (hf : ContinuousOn f s)
    (h₁ : ∀ w : ℂ, DifferentiableOn ℂ (fun v => f (v, w)) ((fun v => (v, w)) ⁻¹' s))
    (h₂ : ∀ v : ℂ, DifferentiableOn ℂ (fun w => f (v, w)) ((fun w => (v, w)) ⁻¹' s)) :
    AnalyticOnNhd ℂ f s := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz)
  let g : ℂ × ℂ → ℂ := fun w => f (z + w)
  have hmem (w : ℂ × ℂ) (hw : w ∈ closedBall (0 : ℂ) r ×ˢ closedBall 0 r) :
      z + w ∈ s := by
    apply hball
    have hw' : w ∈ closedBall (0 : ℂ × ℂ) r := by
      simpa only [Prod.zero_eq_mk, closedBall_prod_same] using hw
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw'
  have hgc : ContinuousOn g (closedBall 0 r ×ˢ closedBall 0 r) :=
    hf.comp (continuous_const.add continuous_id).continuousOn hmem
  have hg₁ (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) r) :
      DiffContOnCl ℂ (fun v => g (v, w)) (ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) hr.ne']
    change DifferentiableOn ℂ (fun v => f (z.1 + v, z.2 + w)) (closedBall 0 r)
    apply (h₁ (z.2 + w)).comp
      ((differentiable_const z.1).add differentiable_id).differentiableOn
    intro v hv
    exact hmem (v, w) ⟨hv, hw⟩
  have hg₂ (v : ℂ) (hv : v ∈ closedBall (0 : ℂ) r) :
      DiffContOnCl ℂ (fun w => g (v, w)) (ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) hr.ne']
    change DifferentiableOn ℂ (fun w => f (z.1 + v, z.2 + w)) (closedBall 0 r)
    apply (h₂ (z.1 + v)).comp
      ((differentiable_const z.2).add differentiable_id).differentiableOn
    intro w hw
    exact hmem (v, w) ⟨hv, hw⟩
  have hga₀ : AnalyticAt ℂ g (0 : ℂ × ℂ) :=
    analyticOnNhd_of_diffContOnCl_slices hr hr hgc hg₁ hg₂ 0
      ⟨mem_ball_self hr, mem_ball_self hr⟩
  have hga : AnalyticAt ℂ g (z - z) := by simpa only [sub_self] using hga₀
  have hshift : AnalyticAt ℂ (fun w : ℂ × ℂ => w - z) z :=
    analyticAt_id.sub analyticAt_const
  have hres : AnalyticAt ℂ (fun w => g (w - z)) z :=
    AnalyticAt.comp (f := fun w : ℂ × ℂ => w - z) hga hshift
  have heq : (fun w => g (w - z)) = f := by
    funext w
    dsimp only [g]
    congr 1
    abel
  rwa [heq] at hres

/-- The rectangular version has the familiar slice-domain hypotheses. -/
theorem analyticOnNhd_polydisc_of_continuousOn_of_slices
    {f : ℂ × ℂ → ℂ} {a b : ℂ} {r R : ℝ}
    (hf : ContinuousOn f (ball a r ×ˢ ball b R))
    (h₁ : ∀ w ∈ ball b R, DifferentiableOn ℂ (fun v => f (v, w)) (ball a r))
    (h₂ : ∀ v ∈ ball a r, DifferentiableOn ℂ (fun w => f (v, w)) (ball b R)) :
    AnalyticOnNhd ℂ f (ball a r ×ˢ ball b R) := by
  apply analyticOnNhd_of_continuousOn_of_slices (isOpen_ball.prod isOpen_ball) hf
  · intro w v hv
    exact (h₁ w hv.2 v hv.1).mono (fun _ h => h.1)
  · intro v w hw
    exact (h₂ v hw.1 w hw.2).mono (fun _ h => h.2)

/-- Joint complex differentiability on an open set implies genuine joint
analyticity; this is not the one-variable Mathlib theorem. -/
theorem analyticOnNhd_of_differentiableOn {f : ℂ × ℂ → ℂ} {s : Set (ℂ × ℂ)}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) : AnalyticOnNhd ℂ f s := by
  apply analyticOnNhd_of_continuousOn_of_slices hs hf.continuousOn
  · intro w
    exact hf.comp (differentiable_id.prodMk (differentiable_const w)).differentiableOn
      (fun _ h => h)
  · intro v
    exact hf.comp ((differentiable_const v).prodMk differentiable_id).differentiableOn
      (fun _ h => h)

theorem analyticOnNhd_iff_differentiableOn {f : ℂ × ℂ → ℂ} {s : Set (ℂ × ℂ)}
    (hs : IsOpen s) : AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s :=
  ⟨AnalyticOnNhd.differentiableOn, analyticOnNhd_of_differentiableOn hs⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic
