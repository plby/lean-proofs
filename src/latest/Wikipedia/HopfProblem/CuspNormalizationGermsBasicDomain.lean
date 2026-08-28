import Wikipedia.HopfProblem.CuspNormalizationGermsBasic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected

/-! # The actual analytic germ ring has no zero divisors

The analytic identity principle on a connected ball implies that a product
of two analytic germs is zero only if one factor is zero.  This argument
works on any complex normed vector space, without a finite-dimensionality
or completeness assumption on the source.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A product of analytic functions can vanish as a germ only if one of
the factors vanishes as a germ.  The small connected ball and the identity
principle are applied to the actual functions, not to a formal power-series
model of their germs. -/
theorem eq_zero_or_eq_zero_of_mul_eventuallyEq_zero {f g : E → ℂ} {a : E}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hfg : (f * g) =ᶠ[𝓝 a] 0) : f =ᶠ[𝓝 a] 0 ∨ g =ᶠ[𝓝 a] 0 := by
  classical
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  by_cases hfzero : f =ᶠ[𝓝 a] 0
  · exact Or.inl hfzero
  right
  have hlocal : ∀ᶠ x in 𝓝 a,
      AnalyticAt ℂ f x ∧ AnalyticAt ℂ g x ∧ f x * g x = 0 := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt, hfg] with x hfx hgx hpx
    exact ⟨hfx, hgx, hpx⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  obtain ⟨x, hx, hfx⟩ : ∃ x ∈ Metric.ball a r, f x ≠ 0 := by
    by_contra hnone
    apply hfzero
    filter_upwards [Metric.ball_mem_nhds a hr] with x hx
    by_contra hfx
    exact hnone ⟨x, hx, hfx⟩
  have hgzero : g =ᶠ[𝓝 x] 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx,
      (hball hx).1.continuousAt.eventually_ne hfx] with y hy hfy
    exact (mul_eq_zero.mp (hball hy).2.2).resolve_left hfy
  have hgball : AnalyticOnNhd ℂ g (Metric.ball a r) := fun y hy => (hball hy).2.1
  have hgident : EqOn g 0 (Metric.ball a r) :=
    hgball.eqOn_zero_of_preconnected_of_eventuallyEq_zero Metric.isPreconnected_ball hx hgzero
  filter_upwards [Metric.ball_mem_nhds a hr] with y hy
  exact hgident hy

/-- Being zero in the actual analytic-germ ring means vanishing on a
neighbourhood, not just vanishing at the basepoint. -/
theorem ofAnalytic_eq_zero_iff {a : E} (f : E → ℂ) (hf : AnalyticAt ℂ f a) :
    ofAnalytic f hf = 0 ↔ f =ᶠ[𝓝 a] 0 := by
  change ofAnalytic f hf = ofAnalytic (0 : E → ℂ) analyticAt_const ↔ _
  exact ofAnalytic_eq_iff f 0 hf analyticAt_const

/-- No zero divisors in the actual ring of analytic function germs. -/
instance analyticGerm_noZeroDivisors (a : E) : NoZeroDivisors (AnalyticGerm a) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro φ ψ h
    obtain ⟨f, hf, rfl⟩ := exists_representative φ
    obtain ⟨g, hg, rfl⟩ := exists_representative ψ
    have hfg : (f * g) =ᶠ[𝓝 a] 0 := by
      apply (ofAnalytic_eq_zero_iff (f * g) (hf.mul hg)).mp
      exact (ofAnalytic_mul f g hf hg).trans h
    exact (eq_zero_or_eq_zero_of_mul_eventuallyEq_zero hf hg hfg).imp
      (ofAnalytic_eq_zero_iff f hf).mpr (ofAnalytic_eq_zero_iff g hg).mpr

/-- The actual analytic-germ ring is an integral domain.  This is not an
assertion that it is integrally closed. -/
instance analyticGerm_isDomain (a : E) : IsDomain (AnalyticGerm a) :=
  NoZeroDivisors.to_isDomain _

end Wikipedia.HopfProblem.CuspNormalization.Germs
