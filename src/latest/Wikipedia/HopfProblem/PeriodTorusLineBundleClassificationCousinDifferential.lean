import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationMixedDbar

/-!
# Local antiholomorphic derivative calculus for actual Cousin cochains

The coordinate derivatives depend only on the germ of the function.
At a smooth point they agree near that point with the corresponding
linear projections of the real Fréchet derivative.  This germ identity
gives local smoothness and the real Schwarz theorem gives commutation
of the two actual mixed antiholomorphic derivatives.

No globally smooth extension of a local representative is chosen.
-/

noncomputable section

open Complex Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin

open PeriodTorusLineBundleClassification

/-- The first antiholomorphic coordinate derivative depends only on the
actual local germ, even without a differentiability hypothesis. -/
theorem dbarFirst_congr {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (h : f =ᶠ[𝓝 q] g) : dbarFirst f q = dbarFirst g q := by
  have ht : Tendsto (fun z : ℂ => (z, q.2)) (𝓝 q.1) (𝓝 q) :=
    (continuous_id.prodMk continuous_const).tendsto q.1
  have he : (fun z : ℂ => f (z, q.2)) =ᶠ[𝓝 q.1] (fun z => g (z, q.2)) :=
    h.comp_tendsto ht
  unfold dbarFirst HolomorphicCousin.dbar
  rw [he.fderiv_eq (𝕜 := ℝ)]

/-- The second antiholomorphic coordinate derivative likewise depends
only on the actual local germ. -/
theorem dbarSecond_congr {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (h : f =ᶠ[𝓝 q] g) : dbarSecond f q = dbarSecond g q := by
  have ht : Tendsto (fun w : ℂ => (q.1, w)) (𝓝 q.2) (𝓝 q) :=
    (continuous_const.prodMk continuous_id).tendsto q.2
  have he : (fun w : ℂ => f (q.1, w)) =ᶠ[𝓝 q.2] (fun w => g (q.1, w)) :=
    h.comp_tendsto ht
  unfold dbarSecond HolomorphicCousin.dbar
  rw [he.fderiv_eq (𝕜 := ℝ)]

theorem dbarFirst_eventuallyEq {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (h : f =ᶠ[𝓝 q] g) : dbarFirst f =ᶠ[𝓝 q] dbarFirst g :=
  h.eventuallyEq_nhds.mono fun _ hx => dbarFirst_congr hx

theorem dbarSecond_eventuallyEq {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (h : f =ᶠ[𝓝 q] g) : dbarSecond f =ᶠ[𝓝 q] dbarSecond g :=
  h.eventuallyEq_nhds.mono fun _ hx => dbarSecond_congr hx

/-- Finite local `C¹` regularity identifies the first derivative with
the projection of the joint real differential on a neighborhood. -/
theorem dbarFirst_eventually_eq_linear {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : ContDiffAt ℝ 1 f q) :
    dbarFirst f =ᶠ[𝓝 q] dbarFirstLinear ∘ fderiv ℝ f := by
  filter_upwards [hf.eventually (by simp)] with x hx
  exact dbarFirst_eq_linear (hx.differentiableAt one_ne_zero)

theorem dbarSecond_eventually_eq_linear {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : ContDiffAt ℝ 1 f q) :
    dbarSecond f =ᶠ[𝓝 q] dbarSecondLinear ∘ fderiv ℝ f := by
  filter_upwards [hf.eventually (by simp)] with x hx
  exact dbarSecond_eq_linear (hx.differentiableAt one_ne_zero)

/-- Taking the first coordinate antiholomorphic derivative preserves
smoothness at the given point. -/
theorem contDiffAt_dbarFirst {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : ContDiffAt ℝ ∞ f q) : ContDiffAt ℝ ∞ (dbarFirst f) q := by
  have hlin : ContDiffAt ℝ ∞ (dbarFirstLinear ∘ fderiv ℝ f) q :=
    dbarFirstLinear.contDiff.contDiffAt.comp q (hf.fderiv_right (by simp))
  exact hlin.congr_of_eventuallyEq (dbarFirst_eventually_eq_linear (hf.of_le (by simp)))

/-- Taking the second coordinate antiholomorphic derivative preserves
smoothness at the given point. -/
theorem contDiffAt_dbarSecond {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : ContDiffAt ℝ ∞ f q) : ContDiffAt ℝ ∞ (dbarSecond f) q := by
  have hlin : ContDiffAt ℝ ∞ (dbarSecondLinear ∘ fderiv ℝ f) q :=
    dbarSecondLinear.contDiff.contDiffAt.comp q (hf.fderiv_right (by simp))
  exact hlin.congr_of_eventuallyEq (dbarSecond_eventually_eq_linear (hf.of_le (by simp)))

theorem fderiv_dbarFirst_apply_of_contDiffAt {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : ContDiffAt ℝ ∞ f q) (v : ℂ × ℂ) :
    fderiv ℝ (dbarFirst f) q v =
      dbarFirstLinear (fderiv ℝ (fderiv ℝ f) q v) := by
  have he := dbarFirst_eventually_eq_linear (hf.of_le (by simp))
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) q := hf.fderiv_right (by simp)
  rw [he.fderiv_eq,
    (dbarFirstLinear.hasFDerivAt.comp q (hd.differentiableAt (by simp)).hasFDerivAt).fderiv]
  rfl

theorem fderiv_dbarSecond_apply_of_contDiffAt {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : ContDiffAt ℝ ∞ f q) (v : ℂ × ℂ) :
    fderiv ℝ (dbarSecond f) q v =
      dbarSecondLinear (fderiv ℝ (fderiv ℝ f) q v) := by
  have he := dbarSecond_eventually_eq_linear (hf.of_le (by simp))
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) q := hf.fderiv_right (by simp)
  rw [he.fderiv_eq,
    (dbarSecondLinear.hasFDerivAt.comp q (hd.differentiableAt (by simp)).hasFDerivAt).fderiv]
  rfl

/-- The actual mixed antiholomorphic coordinate derivatives commute at
every smooth point, by symmetry of the second real Fréchet derivative. -/
theorem dbarFirst_dbarSecond_of_contDiffAt {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : ContDiffAt ℝ ∞ f q) :
    dbarFirst (dbarSecond f) q = dbarSecond (dbarFirst f) q := by
  rw [dbarFirst_eq_linear ((contDiffAt_dbarSecond hf).differentiableAt (by simp)),
    dbarSecond_eq_linear ((contDiffAt_dbarFirst hf).differentiableAt (by simp))]
  simp only [dbarFirstLinear_apply, dbarSecondLinear_apply,
    fderiv_dbarFirst_apply_of_contDiffAt hf, fderiv_dbarSecond_apply_of_contDiffAt hf]
  have hs := hf.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs (1, 0) (0, 1), hs (1, 0) (0, I), hs (I, 0) (0, 1), hs (I, 0) (0, I)]
  ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin
