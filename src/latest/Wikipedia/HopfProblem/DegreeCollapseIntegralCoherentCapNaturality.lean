import Wikipedia.HopfProblem.DegreeCollapseIntegralCoherentSupportRestriction

/-!
# Original inclusion squares for caps from coherent integral classes

The same ambient family restricts compatibly to nested open subsets.
Actual pair-map composition and injective integral excision prove the
class identity. Cap naturality and the original direct-limit formulas
then give both the nested and ambient inclusion squares.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport

open FirstHurewicz SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology
open IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] {d : ℕ}
  (c : ClassFamily X d)

theorem capOnOpen_of (hc : Compatible X d c) (U : Set X) (hU : IsOpen U)
    {p q : ℕ} (h : p + q = d) (K : Compacts U) (a : Component U p K) :
    capOnOpen U hU c hc h (of U p K a) =
      IntegralCompactSupportCap.componentMap (K : Set U) h (restrictToOpen U hU c K) a := rfl

theorem component_inclusion (U : Set X) (hU : IsOpen U) (K : Compacts U)
    {p q : ℕ} (h : p + q = d) (a : Component U p K) :
    singularHomologyMap (subtypeInclusion U) q
        (IntegralCompactSupportCap.componentMap (K : Set U) h (restrictToOpen U hU c K) a) =
      IntegralCompactSupportCap.componentMap (imageCompact U K : Set X) h
        (c (imageCompact U K))
        (IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p a) := by
  have he := RelativeIntegralCap.capProductInDegree_naturality (subtypeInclusion U)
    (IntegralOpenSupport.inclusion_mapsTo U (K : Set U)) h
    (IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p a) (restrictToOpen U hU c K)
  change singularHomologyMap (subtypeInclusion U) q
      (RelativeIntegralCap.capProductInDegree (K : Set U)ᶜ h
        (IntegralOpenSupport.restrictionEquiv U hU (K : Set U) K.isCompact p
          (IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p a))
        (restrictToOpen U hU c K)) =
    RelativeIntegralCap.capProductInDegree (imageCompact U K : Set X)ᶜ h
      (IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p a)
      (IntegralOpenSupport.inclusionMap U (K : Set U) d (restrictToOpen U hU c K)) at he
  rw [IntegralOpenSupport.restriction_extension, restrictToOpen_inclusion] at he
  exact he

theorem withClasses_inclusion (hc : Compatible X d c) (U : Set X) (hU : IsOpen U)
    {p q : ℕ} (h : p + q = d) (a : Cohomology U p) :
    singularHomologyMap (subtypeInclusion U) q (capOnOpen U hU c hc h a) =
      IntegralCompactSupportCap.withClasses h c hc (inclusion U hU p a) := by
  obtain ⟨K, b, rfl⟩ := exists_representative U p a
  have ht := (congrArg (IntegralCompactSupportCap.withClasses h c hc)
    (inclusion_of U hU p K b)).trans
      (IntegralCompactSupportCap.withClasses_of h c hc (imageCompact U K)
        (IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p b))
  exact (congrArg (singularHomologyMap (subtypeInclusion U) q)
    (capOnOpen_of c hc U hU h K b)).trans
      ((component_inclusion c U hU K h b).trans ht.symm)

/-- Nested original pair inclusions preserve the family induced by the same ambient classes. -/
theorem restrictToOpen_subsetInclusion {U V : Set X} (hUV : U ⊆ V)
    (hU : IsOpen U) (hV : IsOpen V) (K : Compacts U) :
    IntegralOpenEmbeddingSupport.map (subsetInclusion hUV)
      (subsetInclusion_isOpenEmbedding hUV hU) (K : Set U)
      (mapCompact (subsetInclusion hUV) K : Set V) rfl d (restrictToOpen U hU c K) =
      restrictToOpen V hV c (mapCompact (subsetInclusion hUV) K) := by
  let f := subsetInclusion hUV
  let hf := subsetInclusion_isOpenEmbedding hUV hU
  let g := subtypeInclusion V
  let hg : Topology.IsOpenEmbedding g := hV.isOpenEmbedding_subtypeVal
  let L := mapCompact f K
  let P := imageCompact U K
  have hP : g '' (L : Set V) = (P : Set X) := Set.image_image g f (K : Set U)
  have hgf : (g.comp f) '' (K : Set U) = (P : Set X) := rfl
  let e := IntegralOpenEmbeddingSupport.mapEquiv g hg (L : Set V) L.isCompact
    (P : Set X) hP d
  have he := (IntegralOpenEmbeddingSupport.map_comp f hf g hg (K : Set U) (L : Set V)
    (P : Set X) rfl hP hgf d (restrictToOpen U hU c K)).symm
  exact e.injective (he.trans ((restrictToOpen_inclusion U hU c K).trans
    (restrictToOpen_inclusion_as V hV c L P hP).symm))

theorem component_subsetInclusion {U V : Set X} (hUV : U ⊆ V)
    (hU : IsOpen U) (hV : IsOpen V) (K : Compacts U)
    {p q : ℕ} (h : p + q = d) (a : Component U p K) :
    singularHomologyMap (subsetInclusion hUV) q
      (IntegralCompactSupportCap.componentMap (K : Set U) h (restrictToOpen U hU c K) a) =
    IntegralCompactSupportCap.componentMap (mapCompact (subsetInclusion hUV) K : Set V) h
      (restrictToOpen V hV c (mapCompact (subsetInclusion hUV) K))
      (IntegralOpenEmbeddingSupport.extension (subsetInclusion hUV)
        (subsetInclusion_isOpenEmbedding hUV hU) (K : Set U) K.isCompact
        (mapCompact (subsetInclusion hUV) K : Set V) rfl p a) := by
  let f := subsetInclusion hUV
  let hf := subsetInclusion_isOpenEmbedding hUV hU
  let L := mapCompact f K
  have he := RelativeIntegralCap.capProductInDegree_naturality f
    (IntegralOpenEmbeddingSupport.mapsTo_compl f hf (K : Set U) (L : Set V) rfl) h
    (IntegralOpenEmbeddingSupport.extension f hf (K : Set U) K.isCompact (L : Set V) rfl p a)
    (restrictToOpen U hU c K)
  change singularHomologyMap f q
      (RelativeIntegralCap.capProductInDegree (K : Set U)ᶜ h
        (IntegralOpenEmbeddingSupport.restrictionEquiv f hf (K : Set U) K.isCompact
          (L : Set V) rfl p
          (IntegralOpenEmbeddingSupport.extension f hf (K : Set U) K.isCompact (L : Set V) rfl p a))
        (restrictToOpen U hU c K)) =
    RelativeIntegralCap.capProductInDegree (L : Set V)ᶜ h
      (IntegralOpenEmbeddingSupport.extension f hf (K : Set U) K.isCompact (L : Set V) rfl p a)
      (IntegralOpenEmbeddingSupport.map f hf (K : Set U) (L : Set V) rfl d
        (restrictToOpen U hU c K)) at he
  have hr := IntegralOpenEmbeddingSupport.restriction_extension f hf (K : Set U) K.isCompact
    (L : Set V) rfl p a
  have hclass := restrictToOpen_subsetInclusion c hUV hU hV K
  exact (congrArg (fun b : IntegralSupportedCohomology.Cohomology (K : Set U) p =>
    singularHomologyMap f q
      (RelativeIntegralCap.capProductInDegree (K : Set U)ᶜ h b (restrictToOpen U hU c K)))
        hr.symm).trans
    (he.trans (congrArg (fun z => RelativeIntegralCap.capProductInDegree (L : Set V)ᶜ h
      (IntegralOpenEmbeddingSupport.extension f hf (K : Set U) K.isCompact (L : Set V) rfl p a) z)
        hclass))

theorem capOnOpen_subsetInclusion (hc : Compatible X d c) {U V : Set X} (hUV : U ⊆ V)
    (hU : IsOpen U) (hV : IsOpen V) {p q : ℕ} (h : p + q = d) (a : Cohomology U p) :
    singularHomologyMap (subsetInclusion hUV) q (capOnOpen U hU c hc h a) =
      capOnOpen V hV c hc h
        (openMap (subsetInclusion hUV) (subsetInclusion_isOpenEmbedding hUV hU) p a) := by
  obtain ⟨K, b, rfl⟩ := exists_representative U p a
  let f := subsetInclusion hUV
  let hf := subsetInclusion_isOpenEmbedding hUV hU
  let L := mapCompact f K
  have ht := (congrArg (capOnOpen V hV c hc h) (openMap_of f hf p K b)).trans
    (capOnOpen_of c hc V hV h L
      (IntegralOpenEmbeddingSupport.extension f hf (K : Set U) K.isCompact (L : Set V) rfl p b))
  exact (congrArg (singularHomologyMap f q) (capOnOpen_of c hc U hU h K b)).trans
    ((component_subsetInclusion c hUV hU hV K h b).trans ht.symm)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport
