import Wikipedia.HopfProblem.RiemannMappingHurwitzFactorization

/-!
# Polynomially weighted Cauchy integrals

The simple-pole contribution to a weighted logarithmic derivative is the
corresponding power of its pole. A nonvanishing analytic factor contributes
zero, since its logarithmic derivative remains analytic on the closed disc.
-/

open Set Metric
open scoped Topology

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.ArgumentPrinciple

/-- A pole strictly inside the disc does not obstruct integrability on
its boundary, including after multiplication by any polynomial weight. -/
theorem circleIntegrable_pow_mul_div_sub {c a : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : a ∈ ball c R) (m : ℂ) (k : ℕ) :
    CircleIntegrable (fun w => w ^ k * (m / (w - a))) c R := by
  have hne : ∀ w ∈ sphere c R, w - a ≠ 0 := by
    intro w hw hwa
    have hwa' : w = a := sub_eq_zero.mp hwa
    subst w
    exact (ne_of_lt (mem_ball.mp ha)) (mem_sphere.mp hw)
  exact ((continuousOn_id.pow k).mul
    (continuousOn_const.div (continuousOn_id.sub continuousOn_const) hne)).circleIntegrable hR.le

/-- Cauchy's integral formula for the polynomially weighted contribution
of one zero of a holomorphic function. -/
theorem circleIntegral_pow_mul_div_sub {c a : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : a ∈ ball c R) (m : ℂ) (k : ℕ) :
    (∮ w in C(c, R), w ^ k * (m / (w - a))) =
      (2 * Real.pi * Complex.I) * (m * a ^ k) := by
  calc
    (∮ w in C(c, R), w ^ k * (m / (w - a))) =
        ∮ w in C(c, R), (m * w ^ k) / (w - a) := by
      apply circleIntegral.integral_congr hR.le
      intro w _
      ring
    _ = (2 * Real.pi * Complex.I) * (m * a ^ k) :=
      Complex.circleIntegral_div_sub_of_differentiable_on_off_countable
        countable_empty ha (by fun_prop) (by intros; fun_prop)

/-- The weighted logarithmic derivative of a nonvanishing analytic factor
is integrable on the disc boundary. -/
theorem circleIntegrable_pow_mul_logDeriv {c : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hg₀ : ∀ z ∈ closedBall c R, g z ≠ 0) (k : ℕ) :
    CircleIntegrable (fun w => w ^ k * logDeriv g w) c R := by
  have hlog : AnalyticOnNhd ℂ (logDeriv g) (closedBall c R) := hg.deriv.div hg hg₀
  have hpow : AnalyticOnNhd ℂ (fun w : ℂ => w ^ k) (closedBall c R) :=
    analyticOnNhd_id.pow k
  exact ((hpow.mul hlog).continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le

/-- A nonvanishing analytic factor contributes zero to every polynomially
weighted argument-principle integral. -/
theorem circleIntegral_pow_mul_logDeriv_eq_zero {c : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hg₀ : ∀ z ∈ closedBall c R, g z ≠ 0) (k : ℕ) :
    (∮ w in C(c, R), w ^ k * logDeriv g w) = 0 := by
  have hlog : AnalyticOnNhd ℂ (logDeriv g) (closedBall c R) := hg.deriv.div hg hg₀
  have hpow : AnalyticOnNhd ℂ (fun w : ℂ => w ^ k) (closedBall c R) :=
    analyticOnNhd_id.pow k
  exact DiffContOnCl.circleIntegral_eq_zero hR.le
    ((hpow.mul hlog).differentiableOn.diffContOnCl_ball subset_rfl)

end Wikipedia.HopfProblem.AnalyticGermsFactorial.ArgumentPrinciple
