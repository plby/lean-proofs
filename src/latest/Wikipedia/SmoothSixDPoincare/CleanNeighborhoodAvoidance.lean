import Wikipedia.SmoothSixDPoincare.CompactEmbeddedAvoidance
import Wikipedia.SmoothSixDPoincare.TwoDimensionalEmbedding

/-!
# Embedded obstacle avoidance relative to an already clean boundary neighborhood

The fixed closed neighborhood may meet the obstacle on the prescribed boundary
set `B`, but nowhere else in the compact source region. Since `B` is inside
the neighborhood's interior, the remaining compact region can be moved off
the obstacle while fixing the whole neighborhood and preserving embeddedness.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {E E' G H H' Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [LindelofSpace (E × Y)]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- An embedded immersive compact region can be made disjoint from the obstacle away from
`B`, fixing its entire prescribed clean closed neighborhood. -/
theorem exists_embedded_image_avoidance_relative_neighborhood
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y)
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A))
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K C B : Set E} (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C)
    (hinj : InjOn f K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ g '' A)
    {O : Set N} (hO : IsOpen O) (hmaps : MapsTo f K O) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧ MapsTo f' K O ∧
      ∀ x ∈ K \ B, f' x ∉ g '' A := by
  let L : Set E := K \ interior C
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A := by
    intro x hx
    exact hclean x ⟨hx.1.1, hx.2⟩ (fun hxB => hx.1.2 (hBC hxB))
  obtain ⟨f', hf', hhom, hemb, hderiv', -, hmaps', havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image f g A hf hg hclosed hself hobstacle
      hK hL hC hinj hderiv hfixed hO hmaps
  refine ⟨f', hf', hhom, hemb, hderiv', hmaps', ?_⟩
  intro x hx
  by_cases hxC : x ∈ C
  · exact havoid x (Or.inl (hclean x ⟨hx.1, hxC⟩ hx.2))
  · exact havoid x (Or.inr ⟨hx.1, fun hi => hxC (interior_subset hi)⟩)

/-- Closed full-image avoidance fixing a clean neighborhood, without an extra open constraint. -/
theorem exists_embedded_avoidance_relative_neighborhood_of_isClosed_range
    (f : C(E, N)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (range g))
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K C B : Set E} (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C)
    (hinj : InjOn f K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ range g) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      ∀ x ∈ K \ B, f' x ∉ range g := by
  obtain ⟨f', hf', hhom, hemb, hd, -, havoid⟩ :=
    exists_embedded_image_avoidance_relative_neighborhood f g univ hf hg
      (by simpa only [image_univ] using hclosed) hself hobstacle hK hC hBC hinj hderiv
      (by simpa only [image_univ] using hclean) isOpen_univ (fun _ _ => mem_univ _)
  refine ⟨f', hf', hhom, hemb, hd, ?_⟩
  simpa only [image_univ] using havoid

/-- For a two-dimensional compact region only the prescribed clean neighborhood need
initially be embedded and immersive. The entire region is then made embedded and its
complement of `B` disjoint from the obstacle, with the whole neighborhood fixed. -/
theorem exists_relative_embedded_avoidance_of_clean_neighborhood_of_isClosed_range
    (f : C(E, N)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (range g))
    (hsourceDim : Module.finrank ℝ E = 2) (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K C B : Set E} (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C)
    (hinj : InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ range g) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      ∀ x ∈ K \ B, f' x ∉ range g := by
  obtain ⟨f₁, hf₁, hhom₁, hemb₁, hderiv₁⟩ :=
    exists_relative_compact_embedding_twoDimensional f hf hsourceDim hdim hK hC hinj hderiv
  have hinj₁ : InjOn f₁ K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb₁.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hclean₁ : ∀ x ∈ K ∩ C, x ∉ B → f₁ x ∉ range g := by
    intro x hx hxB
    rw [← hhom₁.fst_eq_snd hx.2]
    exact hclean x hx hxB
  have hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G := by omega
  obtain ⟨f₂, hf₂, hhom₂, hemb₂, hderiv₂, havoid₂⟩ :=
    exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f₁ g hf₁ hg
      hclosed hself hobstacle
      hK hC hBC hinj₁ hderiv₁ hclean₁
  exact ⟨f₂, hf₂, hhom₁.trans hhom₂, hemb₂, hderiv₂, havoid₂⟩


variable [CompactSpace Y]

/-- Compact-source obstacle avoidance fixing a whole clean closed neighborhood. -/
theorem exists_embedded_avoidance_relative_neighborhood (f : C(E, N)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K C B : Set E} (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C)
    (hinj : InjOn f K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ range g) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      ∀ x ∈ K \ B, f' x ∉ range g :=
  exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f g hf hg
    (isCompact_range g.continuous).isClosed hself hobstacle hK hC hBC hinj hderiv hclean

/-- The two-dimensional relative embedding and avoidance theorem for a compact obstacle. -/
theorem exists_relative_embedded_avoidance_of_clean_neighborhood (f : C(E, N)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hsourceDim : Module.finrank ℝ E = 2) (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K C B : Set E} (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C)
    (hinj : InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ range g) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      ∀ x ∈ K \ B, f' x ∉ range g :=
  exists_relative_embedded_avoidance_of_clean_neighborhood_of_isClosed_range f g hf hg
    (isCompact_range g.continuous).isClosed hsourceDim hdim hobstacle hK hC hBC
    hinj hderiv hclean

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
