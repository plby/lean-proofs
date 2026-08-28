import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# Filter limits for holomorphic normal families

Uniformly Cauchy families with complete targets have uniform limits, for
arbitrary nontrivial index filters. The derivative of a locally uniform limit
is the locally uniform limit of the derivatives when differentiability holds
eventually along that filter.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily

/-- Completeness produces an actual uniform limit on the given set. Values of
the chosen limit outside that set are defined to be zero. -/
theorem exists_tendstoUniformlyOn_of_uniformCauchySeqOn
    {X G ι : Type*} [NormedAddCommGroup G] [CompleteSpace G]
    {φ : Filter ι} [φ.NeBot] {f : ι → X → G} {s : Set X}
    (hf : UniformCauchySeqOn f φ s) :
    ∃ g : X → G, TendstoUniformlyOn f g φ s := by
  classical
  have hlim : ∀ x ∈ s, ∃ y : G, Tendsto (fun i => f i x) φ (𝓝 y) := by
    intro x hx
    exact cauchy_map_iff_exists_tendsto.mp (hf.cauchy_map hx)
  let g : X → G := fun x => if hx : x ∈ s then (hlim x hx).choose else 0
  refine ⟨g, hf.tendstoUniformlyOn_of_tendsto ?_⟩
  intro x hx
  simpa only [g, dif_pos hx] using (hlim x hx).choose_spec

/-- The derivative-limit theorem with eventual, rather than universal,
differentiability of the members of the family. -/
theorem hasFDerivAt_of_tendstoLocallyUniformlyOn_eventually_differentiableOn
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {φ : Filter ι} [φ.NeBot] {s : Set E} {f : ι → E → F}
    {g : E → F} {g' : E → E →L[ℂ] F} {x : E}
    (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn (fderiv ℂ ∘ f) g' φ s)
    (hf : ∀ᶠ i in φ, DifferentiableOn ℂ (f i) s)
    (hfg : ∀ y ∈ s, Tendsto (fun i => f i y) φ (𝓝 (g y)))
    (hx : x ∈ s) : HasFDerivAt g (g' x) x := by
  have hderiv : ∀ᶠ p : ι × E in φ ×ˢ 𝓝 x,
      HasFDerivAt (f p.1) (fderiv ℂ (f p.1) p.2) p.2 := by
    apply (hf.prod_mk (hs.mem_nhds hx)).mono
    rintro ⟨i, y⟩ ⟨hi, hy⟩
    exact ((hi y hy).differentiableAt (hs.mem_nhds hy)).hasFDerivAt
  refine hasFDerivAt_of_tendstoUniformlyOnFilter (f' := fderiv ℂ ∘ f) ?_ hderiv
    (eventually_of_mem (hs.mem_nhds hx) hfg)
  simpa only [hs.nhdsWithin_eq hx] using
    tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily
