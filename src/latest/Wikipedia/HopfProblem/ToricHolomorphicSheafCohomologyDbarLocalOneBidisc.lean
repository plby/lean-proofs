import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarLocalOneBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarLocalOneCutoff

/-!
# Actual smooth primitives for forms closed on a larger bidisc

The coefficients are globally smooth, but their closedness is required
only on the larger bidisc. The first cutoff has its entire support in that
bidisc. Thus arbitrary smooth extensions of local coefficients are allowed.
-/

noncomputable section

open Complex Set Metric Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarLocalOne

open PeriodTorusLineBundleClassification

theorem exists_smooth_primitive_on_closedBidisc_of_closedOn
    {f g : ℂ × ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : ℂ × ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hclosed : ∀ q ∈ closedBall x.1 R ×ˢ closedBall x.2 R,
      dbarFirst g q = dbarSecond f q) :
    ∃ u : ℂ × ℂ → ℂ, ContDiff ℝ ∞ u ∧
      ∀ q ∈ closedBall x.1 r ×ˢ closedBall x.2 r,
        dbarFirst u q = f q ∧ dbarSecond u q = g q := by
  obtain ⟨χ₁, hχ₁, hcχ₁, hχ₁one, hχ₁support⟩ :=
    exists_complex_cutoff_between x.1 hr hrR
  obtain ⟨χ₂, hχ₂, hcχ₂, hχ₂one, _⟩ :=
    exists_complex_cutoff_between x.2 hr hrR
  have hloc : ∀ z w, χ₁ z ≠ 0 → w ∈ closedBall x.2 r →
      dbarFirst g (z, w) = dbarSecond f (z, w) := by
    intro z w hz hw
    exact hclosed (z, w)
      ⟨hχ₁support z hz, closedBall_subset_closedBall hrR.le hw⟩
  refine ⟨localDbarPrimitive χ₁ χ₂ f g,
    contDiff_localDbarPrimitive hχ₁ hχ₂ hcχ₁ hcχ₂ hf hg, ?_⟩
  intro q hq
  exact ⟨dbarFirst_localDbarPrimitive hχ₁ hχ₂ hcχ₁ hcχ₂ hf hg q (hχ₁one q.1 hq.1),
    dbarSecond_localDbarPrimitive_of_closedOn hχ₁ hχ₂ hcχ₁ hcχ₂ hf hg
      hloc hχ₂one q hq.2⟩

/-- Global smooth representatives that are closed only near a point have
an actual smooth primitive near that point. -/
theorem exists_smooth_primitive_of_eventually_closed
    {f g : ℂ × ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {x : ℂ × ℂ} (hclosed : ∀ᶠ q in 𝓝 x, dbarFirst g q = dbarSecond f q) :
    ∃ u : ℂ × ℂ → ℂ, ContDiff ℝ ∞ u ∧
      dbarFirst u =ᶠ[𝓝 x] f ∧ dbarSecond u =ᶠ[𝓝 x] g := by
  obtain ⟨R, hR, hRc⟩ := Metric.eventually_nhds_iff_ball.mp hclosed
  have hc : ∀ q ∈ closedBall x.1 (R / 2) ×ˢ closedBall x.2 (R / 2),
      dbarFirst g q = dbarSecond f q := by
    intro q hq
    have hq' : q ∈ closedBall x (R / 2) := by
      simpa only [closedBall_prod_same] using hq
    have hdist : dist q x ≤ R / 2 := hq'
    exact hRc q (lt_of_le_of_lt hdist (half_lt_self hR))
  obtain ⟨u, hu, hdu⟩ := exists_smooth_primitive_on_closedBidisc_of_closedOn
    hf hg x (show 0 < R / 4 by positivity) (show R / 4 < R / 2 by linarith) hc
  have he : ∀ᶠ q in 𝓝 x, dbarFirst u q = f q ∧ dbarSecond u q = g q := by
    filter_upwards [Metric.ball_mem_nhds x (show 0 < R / 4 by positivity)] with q hq
    apply hdu q
    have hq' := Metric.ball_subset_closedBall hq
    simpa only [closedBall_prod_same] using hq'
  exact ⟨u, hu, he.mono (fun _ h => h.1), he.mono (fun _ h => h.2)⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarLocalOne
