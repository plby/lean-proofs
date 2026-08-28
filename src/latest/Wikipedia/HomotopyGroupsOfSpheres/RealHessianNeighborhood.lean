import Wikipedia.HomotopyGroupsOfSpheres.RealHessianCalculus
import Wikipedia.NoExoticSixSphere.NegativeFormNeighborhood

/-! # A negative Hessian family stays uniformly negative on a small ball -/

open Set Filter
open scoped Topology ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_negative_hessian_ball (f : E → ℝ) (L : D →L[ℝ] E)
    (hf : ContDiffAt ℝ ∞ f 0)
    (hneg : ∀ w : D, w ≠ 0 → realHessian f 0 (L w) (L w) < 0)
    (U : Set E) (hU : U ∈ 𝓝 (0 : E)) :
    ∃ c > 0, ∃ ε > 0, ∀ z ∈ Metric.ball (0 : E) ε,
      z ∈ U ∧ ∀ w : D, realHessian f z (L w) (L w) ≤ -c * ‖w‖ ^ 2 := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) 0 :=
    hf.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have hh : ContinuousAt (realHessian f) 0 := hd.continuousAt_fderiv one_ne_zero
  obtain ⟨c, hc, hforms⟩ := NoExoticSixSphere.NegativeFormNeighborhood.exists_uniform_bound
    (D := D) (E := E) (realHessian f 0) L hneg
  have hnear : ∀ᶠ z in 𝓝 (0 : E), ∀ w : D,
      realHessian f z (L w) (L w) ≤ -c * ‖w‖ ^ 2 := hh.eventually hforms
  have hmem : ∀ᶠ z in 𝓝 (0 : E), z ∈ U := hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hmem.and hnear)
  exact ⟨c, hc, ε, hε, fun z hz => hball hz⟩

end Wikipedia.HomotopyGroupsOfSpheres
