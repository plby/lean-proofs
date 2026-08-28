import Wikipedia.HopfProblem.DegreeCollapseGlobalBasinImages
import Wikipedia.HopfProblem.DegreeCollapseDiscreteFamilySmooth
import Wikipedia.SmoothSixDPoincare.CompactEmbeddedAvoidance

/-!
# Relative embedded avoidance of the entire level-crossing obstruction

The exact countable family of endpoint-basin images is packaged as one
smooth map on a discrete product with a common Euclidean model. Its range
is the actual closed complement of the crossing basin. The existing native
relative avoidance theorem therefore moves a compact embedded source into
that basin, retaining its fixed subset and its embedded immersive property.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_embedded_avoidance_into_level_basin
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) {d : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ d)
    (f₀ : C(A, M)) (hf₀ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ f₀)
    (hself : 2 * Module.finrank ℝ A < Module.finrank ℝ E)
    (hobstacle : Module.finrank ℝ A + d < Module.finrank ℝ E)
    {K L C : Set A} (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C)
    (hinj : InjOn f₀ K) (hderiv : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f₀ x))
    (hfixed : ∀ x ∈ L ∩ C, f₀ x ∈ FlowCancellation.levelBasin S.flow f a) :
    ∃ g : C(A, M), ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ g ∧ f₀.HomotopicRel g C ∧
      Topology.IsClosedEmbedding (fun x : K => g x) ∧
      (∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) g x)) ∧
      (∀ x y, g x = g y → f₀ x = f₀ y) ∧
      ∀ x, (f₀ x ∈ FlowCancellation.levelBasin S.flow f a ∨ x ∈ L) →
        g x ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let J := EndpointBasinIndex S a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable J := endpointBasinIndex_countable S a
  let _ : DiscreteTopology J := inferInstance
  let _ : ChartedSpace Z J := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ J := IsManifold.of_discreteTopology ∞
  obtain ⟨b, hb, hcover⟩ := S.exists_endpoint_obstruction_global_images hf a hhigh hlow
  have hs : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞
      (fun p : J × V => b p.1 p.2) := contMDiff_discrete_family b hb
  let B : C(J × V, M) := ⟨fun p => b p.1 p.2, hs.continuous⟩
  have hrange : range B = (FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [levelBasin_compl_eq_endpoint_obstruction S hf hreg, hcover]
    exact range_discrete_family b
  have hclosed : IsClosed (range B) := by
    rw [hrange, levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact isClosed_endpoint_obstruction S hf a
  have hdim : Module.finrank ℝ A + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hobstacle
  have hfixed' : ∀ x ∈ L ∩ C, f₀ x ∉ range B := by
    intro x hx
    rw [hrange, mem_compl_iff, not_not]
    exact hfixed x hx
  obtain ⟨g, hg, hhom, hemb, hder, hnoNew, havoid⟩ :=
    ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_range
      f₀ B hf₀ hs hclosed hself hdim hK hL hC hinj hderiv hfixed'
  refine ⟨g, hg, hhom, hemb, hder, hnoNew, ?_⟩
  intro x hx
  have hx' : f₀ x ∉ range B ∨ x ∈ L := by
    simpa only [hrange, mem_compl_iff, not_not] using hx
  simpa only [hrange, mem_compl_iff, not_not] using havoid x hx'

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
