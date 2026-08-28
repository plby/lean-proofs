import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Removing isolated singularities on complex curves

The usual removable-singularity theorem is transported through a genuine
manifold chart.  A continuous complex-valued function on an open part of a
complex curve is therefore holomorphic if it is holomorphic away from a
finite set.
-/

open Set Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] {f : M → ℂ}

/-- A continuous isolated singularity of a holomorphic function on a complex
curve is removable.  The proof uses the actual chart at the singularity. -/
theorem contMDiffAt_of_continuousAt_of_eventually_punctured {x : M}
    (hc : ContinuousAt f x)
    (hd : ∀ᶠ y in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f y) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hxe : e x ∈ e.target := e.map_source hx
  have hc' : ContinuousAt (f ∘ e.symm) (e x) :=
    (e.symm.continuousAt_iff_continuousAt_comp_right hx).mp hc
  have hp : Tendsto e.symm (𝓝[≠] e x) (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨(e.tendsto_symm hx).mono_left nhdsWithin_le_nhds, ?_⟩
    simpa only [e.left_inv hx, mem_compl_iff, mem_singleton_iff] using
      e.symm.eventually_ne_nhdsWithin hxe
  have hd' : ∀ᶠ z in 𝓝[≠] e x, DifferentiableAt ℂ (f ∘ e.symm) z := by
    filter_upwards [hp.eventually hd,
      eventually_nhdsWithin_of_eventually_nhds (e.open_target.eventually_mem hxe)]
      with z hz hzt
    have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e.symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) x) hzt
    exact (hz.comp z he).contDiffAt.differentiableAt (by simp)
  have ha := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hd' hc'
  have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e x :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) x) hx
  apply (ha.contDiffAt.contMDiffAt.comp x he).congr_of_eventuallyEq
  filter_upwards [e.eventually_left_inverse hx] with y hy
  exact (congrArg f hy).symm

/-- A continuous function on an open part of a complex curve is holomorphic
when its possible nonholomorphic points form a finite set. -/
theorem contMDiffOn_of_continuousOn_of_finite [T1Space M] {U s : Set M}
    (hU : IsOpen U) (hs : s.Finite) (hc : ContinuousOn f U)
    (hd : ∀ x ∈ U, x ∉ s → ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f U := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_of_continuousAt_of_eventually_punctured
    ((hc x hx).continuousAt (hU.mem_nhds hx))
  have hclosed : IsClosed (s \ {x}) := (hs.subset sdiff_subset).isClosed
  have havoid : (s \ {x})ᶜ ∈ 𝓝 x := hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hx),
    nhdsWithin_le_nhds havoid, self_mem_nhdsWithin] with y hy hyavoid hyne
  apply hd y hy
  intro hys
  exact hyavoid ⟨hys, hyne⟩

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
