import Wikipedia.HopfProblem.CuspNormalizationGermsBasicDomain
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalRemovable
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegralCauchy

/-!
# The bounded Cauchy quotient recovers the actual analytic quotient

Slice-wise removable singularities identify the Cauchy integral with the
original quotient off the denominator zero set.  The analytic identity
principle then turns such an off-zero equality into an equality of actual
analytic function germs.
-/

noncomputable section

open Set Filter Topology Metric

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

/-- The actual fixed-circle Cauchy quotient agrees with the given bounded
quotient throughout the open bidisc, wherever its denominator is nonzero. -/
theorem cauchyQuotient_eq_div_of_bounded {f g : ℂ × ℂ → ℂ} {r R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r ×ˢ closedBall 0 R))
    (hbound : ∀ z ∈ closedBall 0 r ×ˢ closedBall 0 R,
      g z ≠ 0 → ‖f z / g z‖ ≤ M)
    (hboundary : ∀ z ∈ closedBall 0 r ×ˢ sphere 0 R, g z ≠ 0)
    {z : ℂ × ℂ} (hz : z ∈ ball 0 r ×ˢ ball 0 R) (hgz : g z ≠ 0) :
    NormalIntegral.cauchyQuotient f g R z = f z / g z := by
  have hfs : AnalyticOnNhd ℂ (fun t : ℂ => f (z.1, t)) (closedBall 0 R) := by
    intro t ht
    exact (hf (z.1, t) ⟨ball_subset_closedBall hz.1, ht⟩).comp₂
      analyticAt_const analyticAt_id
  have hgs : AnalyticOnNhd ℂ (fun t : ℂ => g (z.1, t)) (closedBall 0 R) := by
    intro t ht
    exact (hg (z.1, t) ⟨ball_subset_closedBall hz.1, ht⟩).comp₂
      analyticAt_const analyticAt_id
  exact NormalRemovable.cauchy_quotient_eq hfs hgs
    (fun t ht => hbound (z.1, t) ⟨ball_subset_closedBall hz.1, ht⟩)
    (fun t ht => hboundary (z.1, t) ⟨ball_subset_closedBall hz.1, ht⟩) hz.2 hgz

/-- Analyticity removes the apparent ambiguity on the denominator zero
set.  The proof uses the actual analytic-germ domain theorem, not a
surrogate rational-function identity. -/
theorem analytic_factorization_of_off_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {a : E} {f g q : E → ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) (hq : AnalyticAt ℂ q a)
    (hgerm : ¬ g =ᶠ[𝓝 a] 0)
    (he : ∀ᶠ z in 𝓝 a, g z ≠ 0 → q z = f z / g z) :
    f =ᶠ[𝓝 a] (fun z => g z * q z) := by
  have hp : (g * (f - g * q)) =ᶠ[𝓝 a] 0 := by
    filter_upwards [he] with z hz
    change g z * (f z - g z * q z) = 0
    by_cases hgz : g z = 0
    · simp only [hgz, zero_mul]
    · have hm : g z * q z = f z := by
        simpa only [mul_comm] using (eq_div_iff hgz).mp (hz hgz)
      rw [hm, sub_self, mul_zero]
  have hzero := (eq_zero_or_eq_zero_of_mul_eventuallyEq_zero hg
    (hf.sub (hg.mul hq)) hp).resolve_left hgerm
  filter_upwards [hzero] with z hz
  exact sub_eq_zero.mp hz

end Wikipedia.HopfProblem.CuspNormalization.Germs
