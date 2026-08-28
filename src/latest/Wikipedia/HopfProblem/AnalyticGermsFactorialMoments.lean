import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegral
import Wikipedia.HopfProblem.RiemannMappingHurwitzFactorization
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Separation.Lemmas

/-!
# Analytic parameter dependence of logarithmic-derivative moments

These are actual fixed-circle integrals of the slices of a jointly analytic
function. Their analyticity follows from the frozen Cauchy quotient theorem,
after expressing the second partial derivative as an evaluation of the
Fréchet derivative. The argument principle then shows that the zeroth moment
is a constant natural number on the first-variable disc.
-/

open Set Metric Filter Topology
open Wikipedia.HopfProblem.CuspNormalization.Germs
open scoped Complex BigOperators

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.Moments

/-- The literal derivative in the second variable. -/
noncomputable def derivW (f : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  deriv (fun w => f (p.1, w)) p.2

/-- The second-variable derivative is the Fréchet derivative evaluated on the
second coordinate vector. -/
theorem derivW_eq_fderiv {f : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hf : DifferentiableAt ℂ f p) :
    derivW f p = fderiv ℂ f p (0, 1) := by
  exact (hf.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

/-- Joint analyticity of the actual second partial derivative. -/
theorem analyticAt_derivW {f : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hf : AnalyticAt ℂ f p) : AnalyticAt ℂ (derivW f) p := by
  have hF : AnalyticAt ℂ (fun q => fderiv ℂ f q (0, 1)) p :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)).analyticAt _).comp
      (f := fderiv ℂ f) hf.fderiv
  apply hF.congr
  filter_upwards [hf.eventually_analyticAt] with q hq
  exact (derivW_eq_fderiv hq.differentiableAt).symm

theorem analyticOnNhd_derivW {f : ℂ × ℂ → ℂ} {s : Set (ℂ × ℂ)}
    (hf : AnalyticOnNhd ℂ f s) : AnalyticOnNhd ℂ (derivW f) s :=
  fun p hp => analyticAt_derivW (hf p hp)

/-- The normalized weighted logarithmic-derivative integral on a fixed circle. -/
noncomputable def moment (f : ℂ × ℂ → ℂ) (R : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∮ w in C(0, R), w ^ k * deriv (fun t => f (z, t)) w / f (z, w)

theorem moment_eq_logDeriv (f : ℂ × ℂ → ℂ) (R : ℝ) (k : ℕ) (z : ℂ) :
    moment f R k z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∮ w in C(0, R), w ^ k * logDeriv (fun t => f (z, t)) w := by
  simp only [moment, logDeriv, Pi.div_apply, mul_div_assoc]

/-- One extra power in the numerator cancels the Cauchy kernel at zero. -/
theorem moment_eq_cauchyQuotient {f : ℂ × ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (k : ℕ) (z : ℂ) :
    moment f R k z = NormalIntegral.cauchyQuotient
      (fun p => p.2 ^ (k + 1) * derivW f p) f R (z, 0) := by
  unfold moment NormalIntegral.cauchyQuotient
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro w hw
  have hw0 : w ≠ 0 := by
    intro h
    exact hR.ne (by simpa [h] using hw)
  simp only [sub_zero, derivW]
  rw [pow_succ]
  field_simp

/-- Every weighted moment is analytic in the parameter. Nonvanishing is needed
only on the boundary cylinder, not inside the second-variable disc. -/
theorem moment_analyticOnNhd {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0) (k : ℕ) :
    AnalyticOnNhd ℂ (moment f R k) (ball 0 r) := by
  have hp : AnalyticOnNhd ℂ (fun p => p.2 ^ (k + 1) * derivW f p)
      (closedBall 0 r ×ˢ closedBall 0 R) :=
    (analyticOnNhd_snd.pow (k + 1)).mul (analyticOnNhd_derivW hf)
  have hQ := NormalIntegral.cauchyQuotient_analyticOnNhd hr hR hp hf hf0
  intro z hz
  have h : AnalyticAt ℂ
      (fun v => NormalIntegral.cauchyQuotient
        (fun p => p.2 ^ (k + 1) * derivW f p) f R (v, 0)) z :=
    (hQ (z, 0) ⟨hz, mem_ball_self hR⟩).comp (f := fun v : ℂ => (v, 0))
      (analyticAt_id.prod analyticAt_const)
  exact h.congr (Filter.Eventually.of_forall fun v => (moment_eq_cauchyQuotient hR k v).symm)

theorem moment_analyticAt_zero {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (moment f R k) 0 :=
  moment_analyticOnNhd hr hR hf hf0 k 0 (mem_ball_self hr)

/-- The zeroth moment is the actual zero count, with analytic multiplicity. -/
theorem moment_zero_eq_finsum {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall 0 r) :
    moment f R 0 z =
      ((∑ᶠ w ∈ ball (0 : ℂ) R,
        analyticOrderNatAt (fun t => f (z, t)) w : ℕ) : ℂ) := by
  have hslice : AnalyticOnNhd ℂ (fun t => f (z, t)) (closedBall 0 R) := by
    intro w hw
    exact (hf (z, w) ⟨hz, hw⟩).comp (f := fun t : ℂ => (z, t))
      (analyticAt_const.prod analyticAt_id)
  have hC : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  unfold moment
  simp only [pow_zero, one_mul]
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    (∮ w in C(0, R), logDeriv (fun t => f (z, t)) w) = _
  rw [Complex.circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd hslice
    (fun w hw => hf0 (z, w) ⟨hz, hw⟩) hR.le]
  exact inv_mul_cancel_left₀ hC _

theorem moment_zero_mem_natCast {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall 0 r) :
    ∃ n : ℕ, moment f R 0 z = n :=
  ⟨_, moment_zero_eq_finsum hR hf hf0 hz⟩

/-- The zero count is constant throughout the connected parameter disc. -/
theorem moment_zero_eq_zero_slice {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 r) : moment f R 0 z = moment f R 0 0 := by
  have hc := (moment_analyticOnNhd hr hR hf hf0 0).continuousOn
  have himg : moment f R 0 '' ball (0 : ℂ) r ⊆ Set.range (fun n : ℕ => (n : ℂ)) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨n, hn⟩ := moment_zero_mem_natCast hR hf hf0 (ball_subset_closedBall hw)
    exact ⟨n, hn.symm⟩
  have hsub := (Set.countable_range (fun n : ℕ => (n : ℂ))).isTotallyDisconnected
    (moment f R 0 '' ball (0 : ℂ) r) himg (isPreconnected_ball.image _ hc)
  exact hsub ⟨z, hz, rfl⟩ ⟨0, mem_ball_self hr, rfl⟩

theorem moment_zero_eventually_eq {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0) :
    moment f R 0 =ᶠ[𝓝 0] fun _ => moment f R 0 0 := by
  filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
  exact moment_zero_eq_zero_slice hr hR hf hf0 hz

/-- A natural-number zero count and the neighborhood on which it is constant. -/
theorem moment_zero_locally_constant {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0) :
    ∃ d : ℕ, moment f R 0 0 = d ∧ ∀ᶠ z in 𝓝 0, moment f R 0 z = d := by
  obtain ⟨d, hd⟩ := moment_zero_mem_natCast hR hf hf0 (mem_closedBall_self hr.le)
  refine ⟨d, hd, ?_⟩
  filter_upwards [moment_zero_eventually_eq hr hR hf hf0] with z hz
  exact hz.trans hd

end Wikipedia.HopfProblem.AnalyticGermsFactorial.Moments
