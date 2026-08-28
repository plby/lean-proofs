import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Order

/-!
# Bounded one-variable quotients and their actual Cauchy extensions

The punctured-neighbourhood limit regularizes a locally bounded
meromorphic function.  The regularization is genuinely analytic, and on
a closed disc with zero-free denominator on its boundary the Cauchy
integral of an analytic quotient equals that quotient wherever the
denominator is nonzero.  This is the one-variable step in the analytic
germ normality argument.
-/

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.NormalRemovable

/-- The actual removable value, defined through the punctured limit. -/
def regularize (f : ℂ → ℂ) (z : ℂ) : ℂ := limUnder (𝓝[≠] z) f

theorem regularize_eq_of_continuousAt {f : ℂ → ℂ} {z : ℂ}
    (hf : ContinuousAt f z) : regularize f z = f z :=
  (hf.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

theorem regularize_eventuallyEq_of_analyticAt {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) : regularize f =ᶠ[𝓝 z] f := by
  filter_upwards [hf.eventually_analyticAt] with w hw
  exact regularize_eq_of_continuousAt hw.continuousAt

theorem regularize_analyticAt_of_analyticAt {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (regularize f) z :=
  hf.congr (regularize_eventuallyEq_of_analyticAt hf).symm

/-- Near a meromorphic point all other points are analytic, so the
pointwise regularization is exactly the one-point removable update. -/
theorem regularize_eventuallyEq_update {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) :
    regularize f =ᶠ[𝓝 z] Function.update f z (regularize f z) := by
  classical
  have he := eventually_nhdsWithin_iff.mp hf.eventually_analyticAt
  filter_upwards [he] with w hw
  by_cases hwz : w = z
  · subst w
    simp
  · rw [Function.update_of_ne hwz]
    exact regularize_eq_of_continuousAt (hw hwz).continuousAt

/-- A local bound and meromorphicity produce an actual analytic
regularization, using only the proved one-variable removable theorem. -/
theorem regularize_analyticAt_of_locally_bounded {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) {M : ℝ} (hM : ∀ᶠ w in 𝓝 z, ‖f w‖ ≤ M) :
    AnalyticAt ℂ (regularize f) z := by
  classical
  have hd : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ f w :=
    hf.eventually_analyticAt.mono fun _ hw => hw.differentiableAt
  have hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] z) (fun w => ‖f w - f z‖) := by
    refine ⟨M + ‖f z‖, eventually_map.mpr ?_⟩
    filter_upwards [hM.filter_mono nhdsWithin_le_nhds] with w hw
    exact norm_sub_le_of_le hw le_rfl
  have ht : Tendsto f (𝓝[≠] z) (𝓝 (regularize f z)) :=
    Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd hb
  have hc : ContinuousAt (Function.update f z (regularize f z)) z :=
    continuousAt_update_same.mpr ht
  exact ((hf.update z (regularize f z)).analyticAt hc).congr
    (regularize_eventuallyEq_update hf).symm

/-- A bounded quotient of analytic functions on a disc has an actual
analytic regularization on the whole closed disc when its boundary
denominator is nonzero.  No isolated-zero set is assumed. -/
theorem regularize_quotient_analyticOnNhd {f g : ℂ → ℂ} {R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hbound : ∀ z ∈ closedBall 0 R, g z ≠ 0 → ‖f z / g z‖ ≤ M)
    (hboundary : ∀ z ∈ sphere 0 R, g z ≠ 0) :
    AnalyticOnNhd ℂ (regularize (fun z => f z / g z)) (closedBall 0 R) := by
  intro z hz
  by_cases hzball : z ∈ ball 0 R
  · apply regularize_analyticAt_of_locally_bounded ((hf z hz).meromorphicAt.div
      (hg z hz).meromorphicAt) (M := max M 0)
    filter_upwards [isOpen_ball.mem_nhds hzball] with w hw
    change ‖f w / g w‖ ≤ max M 0
    by_cases hgw : g w = 0
    · simp only [hgw, div_zero, norm_zero]
      exact le_max_right M 0
    · exact (hbound w (ball_subset_closedBall hw) hgw).trans (le_max_left M 0)
  · have hzsphere : z ∈ sphere 0 R := by
      rw [mem_sphere]
      exact le_antisymm (mem_closedBall.mp hz) (not_lt.mp hzball)
    exact regularize_analyticAt_of_analyticAt
      ((hf z hz).div (hg z hz) (hboundary z hzsphere))

/-- The normalized actual Cauchy integral recovers the bounded quotient
at every interior point with nonzero denominator. -/
theorem cauchy_quotient_eq {f g : ℂ → ℂ} {R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hbound : ∀ z ∈ closedBall 0 R, g z ≠ 0 → ‖f z / g z‖ ≤ M)
    (hboundary : ∀ z ∈ sphere 0 R, g z ≠ 0)
    {w : ℂ} (hw : w ∈ ball 0 R) (hgw : g w ≠ 0) :
    (2 * π * Complex.I : ℂ)⁻¹ *
        (∮ z in C(0, R), (z - w)⁻¹ * (f z / g z)) = f w / g w := by
  let F := regularize (fun z => f z / g z)
  have hF : AnalyticOnNhd ℂ F (closedBall 0 R) :=
    regularize_quotient_analyticOnNhd hf hg hbound hboundary
  have hdiff := hF.differentiableOn.diffContOnCl_ball (Subset.refl (closedBall 0 R))
  have hC := hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hint : (∮ z in C(0, R), (z - w)⁻¹ * (f z / g z)) =
      ∮ z in C(0, R), (z - w)⁻¹ * F z := by
    apply circleIntegral.integral_congr (pos_of_mem_ball hw).le
    intro z hz
    change (z - w)⁻¹ * (f z / g z) = (z - w)⁻¹ * F z
    congr 1
    exact (regularize_eq_of_continuousAt
      ((hf z (sphere_subset_closedBall hz)).div (hg z (sphere_subset_closedBall hz))
        (hboundary z hz)).continuousAt).symm
  rw [hint]
  have hFw : F w = f w / g w := regularize_eq_of_continuousAt
    ((hf w (ball_subset_closedBall hw)).div (hg w (ball_subset_closedBall hw)) hgw).continuousAt
  simpa only [smul_eq_mul, hFw] using hC

end Wikipedia.HopfProblem.CuspNormalization.Germs.NormalRemovable
