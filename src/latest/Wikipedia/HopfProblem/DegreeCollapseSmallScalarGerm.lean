import Wikipedia.HopfProblem.DegreeCollapseLongitudinalExtension

/-!
# Compact scalar germs with arbitrarily small amplitude

A smooth scalar germ vanishing at the origin can be retained in an
arbitrarily small uniformly bounded compact perturbation. Only continuity
controls the amplitude; no vanishing derivative is required. This is the
scalar input for correcting transverse-dependent flight times.
-/

noncomputable section

open Set Function Filter Metric
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Retain a scalar germ with compact support and arbitrarily small uniform amplitude. -/
theorem exists_small_supported_scalar_germ {v : E → ℝ} (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : Set E) (g : E → ℝ), IsCompact K ∧ K ⊆ U ∧ ContDiff ℝ ∞ g ∧
      tsupport g ⊆ K ∧ g =ᶠ[𝓝 0] v ∧ g 0 = 0 ∧ ∀ x, |g x| < ε := by
  have hnear : ∀ᶠ x in 𝓝 (0 : E), x ∈ U ∧ |v x| < ε := by
    have hp : |v 0| < ε := by simpa only [hv0, abs_zero] using hε
    have hmem : ∀ᶠ x in 𝓝 (0 : E), x ∈ U := hU.mem_nhds h0U
    exact hmem.and (hv.continuous.abs.continuousAt (eventually_lt_nhds hp))
  obtain ⟨r, hr, hrsub⟩ := Metric.eventually_nhds_iff.mp hnear
  let β : ContDiffBump (0 : E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let K := closedBall (0 : E) β.rOut
  let g (x : E) := β x * v x
  have hKsmall {x : E} (hx : x ∈ K) : dist x 0 < r := by
    have hh : dist x 0 ≤ r / 2 := hx
    linarith
  have hKU : K ⊆ U := fun _ hx => (hrsub (hKsmall hx)).1
  have hsupp : tsupport g ⊆ K := by
    have hh := tsupport_mul_subset_left (f := fun x : E => β x) (g := v)
    rw [β.tsupport_eq] at hh
    exact hh
  have hgerm : g =ᶠ[𝓝 0] v := by
    filter_upwards [ball_mem_nhds (0 : E) β.rIn_pos] with x hx
    change β x * v x = v x
    rw [β.one_of_mem_closedBall (ball_subset_closedBall hx), one_mul]
  refine ⟨K, g, isCompact_closedBall _ _, hKU, β.contDiff.mul hv, hsupp,
    hgerm, hgerm.eq_of_nhds.trans hv0, ?_⟩
  intro x
  by_cases hx : β x = 0
  · simpa only [g, hx, zero_mul, abs_zero] using hε
  · have hxin : x ∈ K := by
      change x ∈ closedBall (0 : E) β.rOut
      rw [← β.tsupport_eq]
      exact subset_tsupport β hx
    have hvx : |v x| < ε := (hrsub (hKsmall hxin)).2
    change |β x * v x| < ε
    rw [abs_mul, abs_of_nonneg β.nonneg]
    exact (mul_le_of_le_one_left (abs_nonneg (v x)) β.le_one).trans_lt hvx

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
