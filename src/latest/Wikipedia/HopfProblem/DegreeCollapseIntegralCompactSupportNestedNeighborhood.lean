import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportNeighborhood

/-!
# Original integral extensions between nested open neighborhoods

The actual subtype inclusion is an open embedding. Extending an
integral class between two neighborhoods of its compact support equals
restricting the original ambient class directly to the larger one.
Both composites into the ambient compact-support group agree exactly.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {U V : Set X}

def subsetInclusion (hUV : U ⊆ V) : C(U, V) :=
  ⟨Set.inclusion hUV, continuous_subtype_val.subtype_mk _⟩

theorem subsetInclusion_isOpenEmbedding (hUV : U ⊆ V) (hU : IsOpen U) :
    Topology.IsOpenEmbedding (subsetInclusion hUV) :=
  Topology.IsOpenEmbedding.inclusion hUV (hU.preimage continuous_subtype_val)

variable [T2Space X]

omit [T2Space X] in
theorem subsetInclusion_image_inside (hUV : U ⊆ V) (K : Compacts X)
    (hKU : (K : Set X) ⊆ U) (hKV : (K : Set X) ⊆ V) :
    (subsetInclusion hUV) '' (insideCompact U K hKU : Set U) =
      (insideCompact V K hKV : Set V) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨⟨y.val, hKU hy⟩, hy, ?_⟩
    exact Subtype.ext rfl

/-- Original integral inverse excision respects enlargement of the open neighborhood. -/
theorem openMap_neighborhoodOf (hUV : U ⊆ V) (hU : IsOpen U) (hV : IsOpen V)
    (K : Compacts X) (hKU : (K : Set X) ⊆ U) (hKV : (K : Set X) ⊆ V)
    (p : ℕ) (a : Component X p K) :
    openMap (subsetInclusion hUV) (subsetInclusion_isOpenEmbedding hUV hU) p
      (neighborhoodOf U hU K hKU p a) = neighborhoodOf V hV K hKV p a := by
  let N := insideCompact U K hKU
  let P := insideCompact V K hKV
  let f := subsetInclusion hUV
  let hf := subsetInclusion_isOpenEmbedding hUV hU
  let g := subtypeInclusion V
  let hg : Topology.IsOpenEmbedding g := hV.isOpenEmbedding_subtypeVal
  have hP : f '' (N : Set U) = (P : Set V) := subsetInclusion_image_inside hUV K hKU hKV
  have hK : g '' (P : Set V) = (K : Set X) := image_insideCompact V K hKV
  have hgf : (g.comp f) '' (N : Set U) = (K : Set X) := image_insideCompact U K hKU
  have hc := IntegralOpenEmbeddingSupport.restriction_comp f hf g hg
    (N : Set U) N.isCompact (P : Set V) P.isCompact (K : Set X) hP hK hgf p a
  change insideEquiv U hU K hKU p a =
    IntegralOpenEmbeddingSupport.restrictionEquiv f hf (N : Set U) N.isCompact
      (P : Set V) hP p (insideEquiv V hV K hKV p a) at hc
  have he := congrArg
    (IntegralOpenEmbeddingSupport.extension f hf (N : Set U) N.isCompact (P : Set V) hP p) hc
  have he' := he.trans (IntegralOpenEmbeddingSupport.extension_restriction
    f hf (N : Set U) N.isCompact (P : Set V) hP p (insideEquiv V hV K hKV p a))
  exact (openMap_of_image f hf p N P hP (insideEquiv U hU K hKU p a)).trans
    (congrArg (of V p P) he')

/-- Both original composites into ambient integral compact-support cohomology agree. -/
theorem inclusion_subsetInclusion (hUV : U ⊆ V) (hU : IsOpen U) (hV : IsOpen V)
    (p : ℕ) (a : Cohomology U p) :
    inclusion V hV p (openMap (subsetInclusion hUV)
      (subsetInclusion_isOpenEmbedding hUV hU) p a) = inclusion U hU p a := by
  have he := openMap_comp (subsetInclusion hUV) (subsetInclusion_isOpenEmbedding hUV hU)
    (subtypeInclusion V) hV.isOpenEmbedding_subtypeVal p a
  change openMap (subtypeInclusion V) hV.isOpenEmbedding_subtypeVal p
    (openMap (subsetInclusion hUV) (subsetInclusion_isOpenEmbedding hUV hU) p a) =
      openMap (subtypeInclusion U) hU.isOpenEmbedding_subtypeVal p a at he
  rw [openMap_subtype V hV p, openMap_subtype U hU p] at he
  exact he

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology
