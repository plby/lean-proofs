import Wikipedia.HopfProblem.DegreeCollapsePositiveEndpointImages
import Wikipedia.HopfProblem.DegreeCollapseLevelBasinAvoidance
import Wikipedia.SmoothSixDPoincare.OpenObstacleRestriction

/-!
# Embedded endpoint avoidance entirely above the original lower cut

Restrict the actual countable endpoint family to the strict superlevel.
Its image is exactly the original level-crossing obstruction in this open
manifold, hence is closed there. Compact embedded avoidance now takes place
entirely in the strict superlevel, including its relative homotopy. No
dimension bound is required for critical points at or below the lower cut.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap TopologicalSpace
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_embedded_avoidance_into_level_basin_above_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b a : ℝ} (U : Opens M) (hU : ∀ x, x ∈ U ↔ b < f x)
    (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) {d : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p →
      Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, b < f p → f p ≤ a → nativeMorseIndex E f p ≤ d)
    (f₀ : C(A, U)) (hf₀ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ f₀)
    (hself : 2 * Module.finrank ℝ A < Module.finrank ℝ E)
    (hobstacle : Module.finrank ℝ A + d < Module.finrank ℝ E)
    {K L C : Set A} (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C)
    (hinj : InjOn f₀ K) (hderiv : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f₀ x))
    (hfixed : ∀ x ∈ L ∩ C, (f₀ x).val ∈ FlowCancellation.levelBasin S.flow f a) :
    ∃ g : C(A, U), ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ g ∧ f₀.HomotopicRel g C ∧
      Topology.IsClosedEmbedding (fun x : K => g x) ∧
      (∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) g x)) ∧
      (∀ x y, g x = g y → f₀ x = f₀ y) ∧
      ∀ x, ((f₀ x).val ∈ FlowCancellation.levelBasin S.flow f a ∨ x ∈ L) →
        (g x).val ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let J := EndpointBasinIndexAbove S b a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable J := endpointBasinIndexAbove_countable S b a
  let _ : DiscreteTopology J := inferInstance
  let _ : ChartedSpace Z J := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ J := IsManifold.of_discreteTopology ∞
  obtain ⟨gB, hgB, hcover⟩ :=
    S.exists_endpoint_obstruction_images_above_cut hf b a hhigh hlow
  have hs : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞
      (fun p : J × V => gB p.1 p.2) := contMDiff_discrete_family gB hgB
  let B : C(J × V, M) := ⟨fun p => gB p.1 p.2, hs.continuous⟩
  have hrangeB : range B = ⋃ i, range (gB i) := range_discrete_family gB
  let R := OpenObstacle.restrict B U
  have hrange : range R =
      (Subtype.val : U → M) ⁻¹' (FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [OpenObstacle.range_restrict, hrangeB,
      levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    ext x
    exact (hcover x.val ((hU x.val).mp x.property)).symm
  have hclosed : IsClosed (range R) := by
    rw [hrange, levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact (isClosed_endpoint_obstruction S hf a).preimage continuous_subtype_val
  have hdim : Module.finrank ℝ A + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hobstacle
  have hfixed' : ∀ x ∈ L ∩ C, f₀ x ∉ range R := by
    intro x hx
    rw [hrange, mem_preimage, mem_compl_iff, not_not]
    exact hfixed x hx
  obtain ⟨g, hg, hhom, hemb, hder, hnoNew, havoid⟩ :=
    ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_range
      f₀ R hf₀ (OpenObstacle.contMDiff_restrict B U hs) hclosed
      hself hdim hK hL hC hinj hderiv hfixed'
  refine ⟨g, hg, hhom, hemb, hder, hnoNew, ?_⟩
  intro x hx
  have hx' : f₀ x ∉ range R ∨ x ∈ L := by
    simpa only [hrange, mem_preimage, mem_compl_iff, not_not] using hx
  simpa only [hrange, mem_preimage, mem_compl_iff, not_not] using havoid x hx'

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
