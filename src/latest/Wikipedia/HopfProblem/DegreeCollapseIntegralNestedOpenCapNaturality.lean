import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportNestedNeighborhood
import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenCapNaturality

/-!
# Exact integral cap compatibility between original nested open subsets

All open-subset classes come from the same constructed ambient class.
Composition of the original pair inclusions, followed by injectivity of
actual integral excision, proves that the nested inclusion preserves
these classes exactly. Integral cap naturality then gives the original
compact-support cap square between the two open subsets.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenFundamentalClass

open FirstHurewicz SingularMayerVietoris NoExoticSixSphere
open IntegralCompactSupportCohomology (subsetInclusion subsetInclusion_isOpenEmbedding)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

/-- Retain any separately named actual image support in the original ambient inclusion. -/
theorem supportedClass_map_inclusion (U : Set M) (hU : IsOpen U)
    (K : Set U) (hK : IsCompact K) (P : Set M) (hP : (subtypeInclusion U) '' K = P) :
    IntegralOpenEmbeddingSupport.map (subtypeInclusion U) hU.isOpenEmbedding_subtypeVal
        K P hP (n + 3) (supportedClass (E := E) n U hU K hK) =
      IntegralManifoldFundamentalClass.supportedClass (E := E) n M P := by
  subst P
  exact supportedClass_inclusion (E := E) n U hU K hK

/-- The original nested pair inclusion preserves the constructed integral class, with no sign. -/
theorem supportedClass_subsetInclusion {U V : Set M} (hUV : U ⊆ V)
    (hU : IsOpen U) (hV : IsOpen V) (K : Set U) (hK : IsCompact K)
    (L : Set V) (hL : (subsetInclusion hUV) '' K = L) :
    IntegralOpenEmbeddingSupport.map (subsetInclusion hUV)
        (subsetInclusion_isOpenEmbedding hUV hU) K L hL (n + 3)
        (supportedClass (E := E) n U hU K hK) =
      supportedClass (E := E) n V hV L (hL ▸ hK.image (subsetInclusion hUV).continuous) := by
  let f := subsetInclusion hUV
  let hf := subsetInclusion_isOpenEmbedding hUV hU
  let g := subtypeInclusion V
  let hg : Topology.IsOpenEmbedding g := hV.isOpenEmbedding_subtypeVal
  let P := IntegralOpenSupport.imageSupport U K
  have hLc : IsCompact L := hL ▸ hK.image f.continuous
  have hP : g '' L = P := by
    rw [← hL]
    exact Set.image_image g f K
  have hgf : (g.comp f) '' K = P := rfl
  apply (IntegralOpenEmbeddingSupport.mapEquiv g hg L hLc P hP (n + 3)).injective
  calc
    _ = IntegralOpenEmbeddingSupport.map (g.comp f) (hg.comp hf) K P hgf (n + 3)
        (supportedClass (E := E) n U hU K hK) :=
      (IntegralOpenEmbeddingSupport.map_comp f hf g hg K L P hL hP hgf (n + 3)
        (supportedClass (E := E) n U hU K hK)).symm
    _ = IntegralManifoldFundamentalClass.supportedClass (E := E) n M P :=
      supportedClass_map_inclusion (E := E) n U hU K hK P rfl
    _ = _ := (supportedClass_map_inclusion (E := E) n V hV L hLc P hP).symm

/-- The genuine component cap square for a nested original open-subspace inclusion. -/
theorem componentMap_subsetInclusion {U V : Set M} (hUV : U ⊆ V)
    (hU : IsOpen U) (hV : IsOpen V) (K : Set U) (hK : IsCompact K)
    (L : Set V) (hL : (subsetInclusion hUV) '' K = L)
    (p q : ℕ) (h : p + q = n + 3) (a : IntegralSupportedCohomology.Cohomology K p) :
    singularHomologyMap (subsetInclusion hUV) q
        (IntegralCompactSupportCap.componentMap K h (supportedClass (E := E) n U hU K hK) a) =
      IntegralCompactSupportCap.componentMap L h
        (supportedClass (E := E) n V hV L (hL ▸ hK.image (subsetInclusion hUV).continuous))
        (IntegralOpenEmbeddingSupport.extension (subsetInclusion hUV)
          (subsetInclusion_isOpenEmbedding hUV hU) K hK L hL p a) := by
  let f := subsetInclusion hUV
  let hf := subsetInclusion_isOpenEmbedding hUV hU
  have he := RelativeIntegralCap.capProductInDegree_naturality f
    (IntegralOpenEmbeddingSupport.mapsTo_compl f hf K L hL) h
    (IntegralOpenEmbeddingSupport.extension f hf K hK L hL p a)
    (supportedClass (E := E) n U hU K hK)
  change singularHomologyMap f q
      (RelativeIntegralCap.capProductInDegree Kᶜ h
        (IntegralOpenEmbeddingSupport.restrictionEquiv f hf K hK L hL p
          (IntegralOpenEmbeddingSupport.extension f hf K hK L hL p a))
        (supportedClass (E := E) n U hU K hK)) =
    RelativeIntegralCap.capProductInDegree Lᶜ h
      (IntegralOpenEmbeddingSupport.extension f hf K hK L hL p a)
      (IntegralOpenEmbeddingSupport.map f hf K L hL (n + 3)
        (supportedClass (E := E) n U hU K hK)) at he
  rw [IntegralOpenEmbeddingSupport.restriction_extension,
    supportedClass_subsetInclusion (E := E) n hUV hU hV] at he
  exact he

/-- Original extension and original homology inclusion intertwine the actual open cap maps. -/
theorem dualityMap_subsetInclusion {U V : Set M} (hUV : U ⊆ V)
    (hU : IsOpen U) (hV : IsOpen V) (p q : ℕ) (h : p + q = n + 3)
    (a : IntegralCompactSupportCohomology.Cohomology U p) :
    singularHomologyMap (subsetInclusion hUV) q (dualityMap (E := E) n U hU p q h a) =
      dualityMap (E := E) n V hV p q h
        (IntegralCompactSupportCohomology.openMap (subsetInclusion hUV)
          (subsetInclusion_isOpenEmbedding hUV hU) p a) := by
  obtain ⟨K, b, rfl⟩ := IntegralCompactSupportCohomology.exists_representative U p a
  let f := subsetInclusion hUV
  let hf := subsetInclusion_isOpenEmbedding hUV hU
  let L := IntegralCompactSupportCohomology.mapCompact f K
  have ht := (congrArg (dualityMap (E := E) n V hV p q h)
    (IntegralCompactSupportCohomology.openMap_of f hf p K b)).trans
      (dualityMap_of (E := E) n V hV p q h L
        (IntegralOpenEmbeddingSupport.extension f hf (K : Set U) K.isCompact
          (L : Set V) rfl p b))
  exact (congrArg (singularHomologyMap f q)
    (dualityMap_of (E := E) n U hU p q h K b)).trans
      ((componentMap_subsetInclusion (E := E) n hUV hU hV (K : Set U) K.isCompact
        (L : Set V) rfl p q h b).trans ht.symm)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenFundamentalClass
