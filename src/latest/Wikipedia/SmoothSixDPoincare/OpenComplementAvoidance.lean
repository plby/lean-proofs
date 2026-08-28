import Wikipedia.SmoothSixDPoincare.OpenObstacleRestriction

/-!
# Relative embedded disk perturbations inside an open complement

All maps and the whole relative homotopy stay in the actual open ambient
submanifold. Avoidance concerns the full original obstacle image, not just a
chosen compact portion of its restricted parameter space.
-/

noncomputable section

open Set ContinuousMap TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {E E' G H H' Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [SecondCountableTopology Y]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- Relative embedding and obstacle avoidance entirely inside an open ambient submanifold. -/
theorem exists_relative_embedded_avoidance_in_open_of_isClosed_range
    (U : Opens N) (f : C(E, U)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (range g))
    (hsourceDim : Module.finrank ℝ E = 2) (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K C B : Set E} (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C)
    (hinj : InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → (f x : N) ∉ range g) :
    ∃ f' : C(E, U), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      ∀ x ∈ K \ B, (f' x : N) ∉ range g := by
  have hclean' : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ range (OpenObstacle.restrict g U) := by
    intro x hx hxB hmem
    exact hclean x hx hxB ((OpenObstacle.mem_range_restrict_iff g U (f x)).mp hmem)
  obtain ⟨f', hf', hhom, hemb, hderiv', havoid⟩ :=
    exists_relative_embedded_avoidance_of_clean_neighborhood_of_isClosed_range
      f (OpenObstacle.restrict g U) hf (OpenObstacle.contMDiff_restrict g U hg)
      (OpenObstacle.isClosed_range_restrict g U hclosed) hsourceDim hdim hobstacle
      hK hC hBC hinj hderiv hclean'
  refine ⟨f', hf', hhom, hemb, hderiv', ?_⟩
  intro x hx hmem
  exact havoid x hx ((OpenObstacle.mem_range_restrict_iff g U (f' x)).mpr hmem)

/-- Avoid a selected closed obstacle image inside `U`, preserving the whole clean neighborhood
and an additional open condition on the compact embedded disk. -/
theorem exists_embedded_image_avoidance_relative_neighborhood_in_open
    (U : Opens N) (f : C(E, U)) (g : C(Y, N)) (A : Set Y)
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A))
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K C B : Set E} (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C)
    (hinj : InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → (f x : N) ∉ g '' A)
    {O : Set U} (hO : IsOpen O) (hmaps : MapsTo f K O) :
    ∃ f' : C(E, U), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧ MapsTo f' K O ∧
      ∀ x ∈ K \ B, (f' x : N) ∉ g '' A := by
  let A' : Set (OpenObstacle.source g U) := Subtype.val ⁻¹' A
  have hclean' : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ OpenObstacle.restrict g U '' A' := by
    intro x hx hxB hmem
    rw [OpenObstacle.image_restrict] at hmem
    exact hclean x hx hxB hmem
  obtain ⟨f', hf', hhom, hemb, hd, hmaps', havoid⟩ :=
    exists_embedded_image_avoidance_relative_neighborhood f (OpenObstacle.restrict g U) A'
      hf (OpenObstacle.contMDiff_restrict g U hg) (OpenObstacle.isClosed_image_restrict g U A
        hclosed) hself hobstacle hK hC hBC hinj hderiv hclean' hO hmaps
  refine ⟨f', hf', hhom, hemb, hd, hmaps', ?_⟩
  intro x hx hmem
  apply havoid x hx
  rw [OpenObstacle.image_restrict]
  exact hmem

omit [SecondCountableTopology Y] in
/-- For a compact obstacle manifold with second-countable model, the required countability
and closed-image hypotheses are consequences of the original native manifold data. -/
theorem exists_relative_embedded_avoidance_in_open
    [CompactSpace Y] [SecondCountableTopology H']
    (U : Opens N) (f : C(E, U)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hsourceDim : Module.finrank ℝ E = 2) (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K C B : Set E} (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C)
    (hinj : InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → (f x : N) ∉ range g) :
    ∃ f' : C(E, U), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      ∀ x ∈ K \ B, (f' x : N) ∉ range g := by
  let : SecondCountableTopology Y := ChartedSpace.secondCountable_of_sigmaCompact H' Y
  exact exists_relative_embedded_avoidance_in_open_of_isClosed_range U f g hf hg
    (isCompact_range g.continuous).isClosed hsourceDim hdim hobstacle hK hC hBC
    hinj hderiv hclean

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
