import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Removable punctures for maps between complex curves

Continuity at the omitted point and holomorphicity on a punctured
neighborhood imply holomorphicity at the point.  Both source and target
use their existing complex manifold charts.  In coordinates, the proof
is the complex removable-singularity theorem; no new manifold structure
or holomorphicity at the omitted point is assumed.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

private theorem openPartialHomeomorph_symm_tendsto_punctured
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {x : X} (hx : x ∈ e.source) :
    Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] x) := by
  refine tendsto_nhdsWithin_iff.mpr
    ⟨(e.tendsto_symm hx).mono_left nhdsWithin_le_nhds, ?_⟩
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, e.left_inv hx] using
    e.symm.eventually_ne_nhdsWithin (e.map_source hx)

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
  [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N]

/-- A continuous puncture of a holomorphic map between actual complex
one-dimensional manifolds is removable. -/
theorem contMDiffAt_of_continuousAt_of_punctured {f : M → N} {x : M}
    (hf : ContinuousAt f x)
    (hd : ∀ᶠ z in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f z) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  let e := chartAt ℂ x
  let e' := chartAt ℂ (f x)
  let F : ℂ → ℂ := e' ∘ f ∘ e.symm
  have hxe : x ∈ e.source := ChartedSpace.mem_chart_source x
  have hye : f x ∈ e'.source := ChartedSpace.mem_chart_source (f x)
  have hcF : ContinuousAt F (e x) := by
    have hcomposed : Tendsto F (𝓝 (e x)) (𝓝 (e' (f x))) :=
      (e'.continuousAt hye).tendsto.comp (hf.tendsto.comp (e.tendsto_symm hxe))
    simpa only [ContinuousAt, F, Function.comp_apply, e.left_inv hxe] using hcomposed
  have hdomain : ∀ᶠ z in 𝓝 (e x), z ∈ e.target :=
    e.open_target.mem_nhds (e.map_source hxe)
  have htarget : ∀ᶠ z in 𝓝 (e x), f (e.symm z) ∈ e'.source :=
    (hf.tendsto.comp (e.tendsto_symm hxe)).eventually (e'.open_source.mem_nhds hye)
  have hdiff : ∀ᶠ z in 𝓝[≠] (e x), DifferentiableAt ℂ F z := by
    filter_upwards [(openPartialHomeomorph_symm_tendsto_punctured e hxe).eventually hd,
      eventually_nhdsWithin_of_eventually_nhds hdomain,
      eventually_nhdsWithin_of_eventually_nhds htarget] with z hz hzDomain hzTarget
    have hcoords : ContDiffAt ℂ ω F (e (e.symm z)) := by
      have h := (contMDiffAt_iff_of_mem_source (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
        (x := x) (y := f x) (e.map_target hzDomain) hzTarget).mp hz
      simpa only [e, e', F, mfld_simps, contDiffWithinAt_univ] using h.2
    rw [e.right_inv hzDomain] at hcoords
    exact hcoords.differentiableAt (by simp)
  have ha := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hdiff hcF
  apply contMDiffAt_iff.mpr
  refine ⟨hf, ?_⟩
  have hsm : ContDiffAt ℂ ω F (e x) := ha.contDiffAt
  simpa only [e, e', F, mfld_simps] using hsm.contDiffWithinAt (s := Set.univ)

end Wikipedia.HopfProblem.TriangleUniformizationGluing
