import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-! # Local propagation of nonzero analytic germs

An analytic function with a nonzero germ at a point has a nonzero germ at
every sufficiently nearby point.  The identity principle on an actual
connected ball proves this without requiring a complete or finite-dimensional
source space.
-/

open Set Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicMeromorphicIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A nonzero analytic germ remains nonzero at every sufficiently nearby
point.  Nonzero here means that the function does not vanish on a whole
neighborhood, not that its value at the basepoint is nonzero. -/
theorem analyticAt_eventually_nonzero_germ {f : E → ℂ} {a : E}
    (hf : AnalyticAt ℂ f a) (hne : ¬ f =ᶠ[𝓝 a] 0) :
    ∀ᶠ x in 𝓝 a, ¬ f =ᶠ[𝓝 x] 0 := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hf.eventually_analyticAt
  have hfball : AnalyticOnNhd ℂ f (Metric.ball a r) := fun x hx => hball hx
  filter_upwards [Metric.ball_mem_nhds a hr] with x hx
  intro hxzero
  apply hne
  have hzero : EqOn f 0 (Metric.ball a r) :=
    hfball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      Metric.isPreconnected_ball hx hxzero
  filter_upwards [Metric.ball_mem_nhds a hr] with y hy
  exact hzero hy

/-- On an open set where a function is analytic, the locus where its germ
is nonzero is open in the ambient normed space. -/
theorem isOpen_nonzero_germ_locus {f : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) :
    IsOpen {a | a ∈ U ∧ ¬ f =ᶠ[𝓝 a] 0} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  filter_upwards [hU.mem_nhds ha.1,
    analyticAt_eventually_nonzero_germ (hf a ha.1) ha.2] with x hx hne
  exact ⟨hx, hne⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphicIdentity
