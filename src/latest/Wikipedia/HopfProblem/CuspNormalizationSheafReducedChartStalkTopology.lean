import Wikipedia.HopfProblem.CuspNormalizationSheafReducedLocality
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Relative germs in genuine ambient charts

An actual open partial homeomorphism transports neighbourhoods along a
subset to neighbourhoods along its actual chart image. Equality of
relative germs is preserved and reflected by this transport.
-/

noncomputable section

open Set Filter Topology TopologicalSpace

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

section Chart

variable {M E : Type} [TopologicalSpace M] [TopologicalSpace E]

/-- The actual part of the subset visible in an ambient chart. -/
def chartSubset (e : OpenPartialHomeomorph M E) (S : Set M) : Set E :=
  e.target ∩ e.symm ⁻¹' S

/-- A point of the subset, expressed in an actual ambient chart. -/
def chartPoint (e : OpenPartialHomeomorph M E) (S : Set M)
    (x : S) (hx : x.val ∈ e.source) : chartSubset e S :=
  ⟨e x.val, e.map_source hx, by
    change e.symm (e x.val) ∈ S
    rw [e.left_inv hx]
    exact x.property⟩

/-- The forward chart map sends actual relative neighbourhoods to
relative neighbourhoods in the chart image. -/
theorem chart_tendsto (e : OpenPartialHomeomorph M E) (S : Set M)
    (x : S) (hx : x.val ∈ e.source) :
    Tendsto e (𝓝[S] x.val) (𝓝[chartSubset e S] (e x.val)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within e
    (e.continuousAt hx).continuousWithinAt ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hx)] with y hyS hySource
  refine ⟨e.map_source hySource, ?_⟩
  change e.symm (e y) ∈ S
  rw [e.left_inv hySource]
  exact hyS

/-- The inverse chart map sends relative neighbourhoods in the chart
image back to actual relative neighbourhoods of the original subset. -/
theorem chart_symm_tendsto (e : OpenPartialHomeomorph M E) (S : Set M)
    (x : S) (hx : x.val ∈ e.source) :
    Tendsto e.symm (𝓝[chartSubset e S] (e x.val)) (𝓝[S] x.val) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within e.symm
    ((e.tendsto_symm hx).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hy.2

/-- Equality of actual relative germs is preserved and reflected by
composition with the inverse of a genuine chart. -/
theorem chart_comp_symm_eventuallyEq_iff (e : OpenPartialHomeomorph M E)
    (S : Set M) (x : S) (hx : x.val ∈ e.source) (f g : M → ℂ) :
    (f ∘ e.symm) =ᶠ[𝓝[chartSubset e S] (e x.val)] (g ∘ e.symm) ↔
      f =ᶠ[𝓝[S] x.val] g := by
  constructor
  · intro h
    have hp := h.comp_tendsto (chart_tendsto e S x hx)
    filter_upwards [hp,
      mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hx)] with y hy hySource
    simpa only [Function.comp_apply, e.left_inv hySource] using hy
  · intro h
    exact h.comp_tendsto (chart_symm_tendsto e S x hx)

end Chart

section Relative

variable {M : Type} [TopologicalSpace M]

/-- The literal zero extension of a complex-valued function on a
relative open set, without imposing any analytic condition. -/
def relativeExtension (S : Set M) (U : Opens S) (f : U → ℂ) (y : M) : ℂ := by
  classical
  exact if hyS : y ∈ S then
    if hyU : (⟨y, hyS⟩ : S) ∈ U then f ⟨⟨y, hyS⟩, hyU⟩ else 0
  else 0

@[simp] theorem relativeExtension_apply (S : Set M) (U : Opens S)
    (f : U → ℂ) (y : M) (hyS : y ∈ S) (hyU : (⟨y, hyS⟩ : S) ∈ U) :
    relativeExtension S U f y = f ⟨⟨y, hyS⟩, hyU⟩ := by
  classical
  simp only [relativeExtension, dif_pos hyS, dif_pos hyU]

/-- Relative open neighbourhoods contain all sufficiently nearby points
of the actual subset in an arbitrary ambient topological space. -/
theorem eventually_mem_openSubset (S : Set M) (x : S) (U : Opens S)
    (hx : x ∈ U) :
    ∀ᶠ y in 𝓝[S] x.val, ∃ hyS : y ∈ S, (⟨y, hyS⟩ : S) ∈ U := by
  obtain ⟨V, hV⟩ := exists_ambient_open S U
  have hxV : x.val ∈ V := by
    change x ∈ Subtype.val ⁻¹' (V : Set M)
    rw [hV]
    exact hx
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hxV)] with y hyS hyV
  refine ⟨hyS, ?_⟩
  change (⟨y, hyS⟩ : S) ∈ (U : Set S)
  rw [← hV]
  exact hyV

end Relative

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
