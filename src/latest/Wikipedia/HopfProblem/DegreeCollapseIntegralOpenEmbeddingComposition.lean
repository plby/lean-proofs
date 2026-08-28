import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenEmbeddingSupport

/-!
# Composition of original integral support maps

Keep the original compact image supports explicitly. Chain-map
composition proves both homology composition and cohomology restriction
composition. Inverting actual excision gives composition of extension.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenEmbeddingSupport

open SingularMayerVietoris SingularCohomologyFree NoExoticSixSphere
open IntegralSupportedCohomology (Cohomology)

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)
  (g : C(Y, Z)) (hg : Topology.IsOpenEmbedding g)

theorem mapChain_comp (K : Set X) (L : Set Y) (P : Set Z)
    (hL : f '' K = L) (hP : g '' L = P) (hgf : (g.comp f) '' K = P) :
    mapChain (g.comp f) (hg.comp hf) K P hgf =
      mapChain f hf K L hL ≫ mapChain g hg L P hP := by
  exact RelativeSingularHomology.mapChain_comp f (mapsTo_compl f hf K L hL)
    g (mapsTo_compl g hg L P hP)

theorem map_comp (K : Set X) (L : Set Y) (P : Set Z)
    (hL : f '' K = L) (hP : g '' L = P) (hgf : (g.comp f) '' K = P) (k : ℕ)
    (a : SupportedRelativeHomology.Homology (ModuleCat.of ℤ ℤ) K k) :
    map (g.comp f) (hg.comp hf) K P hgf k a =
      map g hg L P hP k (map f hf K L hL k a) := by
  have he := congrArg (fun m => homologyLinearMap m k)
    (mapChain_comp f hf g hg K L P hL hP hgf)
  rw [homologyLinearMap_comp] at he
  exact LinearMap.congr_fun he a

theorem restrictionMap_comp (K : Set X) (L : Set Y) (P : Set Z)
    (hL : f '' K = L) (hP : g '' L = P) (hgf : (g.comp f) '' K = P) :
    restrictionMap (g.comp f) (hg.comp hf) K P hgf =
      restrictionMap g hg L P hP ≫ restrictionMap f hf K L hL := by
  exact (congrArg dualMap (mapChain_comp f hf g hg K L P hL hP hgf)).trans
    (dualMap_comp (mapChain f hf K L hL) (mapChain g hg L P hP))

variable [T2Space Y] [T2Space Z]

theorem restriction_comp (K : Set X) (hK : IsCompact K) (L : Set Y) (hLc : IsCompact L)
    (P : Set Z) (hL : f '' K = L) (hP : g '' L = P) (hgf : (g.comp f) '' K = P)
    (p : ℕ) (a : Cohomology P p) :
    restrictionEquiv (g.comp f) (hg.comp hf) K hK P hgf p a =
      restrictionEquiv f hf K hK L hL p (restrictionEquiv g hg L hLc P hP p a) := by
  have he := congrArg (fun m => HomologicalComplex.homologyMap m p)
    (restrictionMap_comp f hf g hg K L P hL hP hgf)
  rw [HomologicalComplex.homologyMap_comp] at he
  exact congrArg (fun m => m.hom a) he

theorem extension_comp (K : Set X) (hK : IsCompact K) (L : Set Y) (hLc : IsCompact L)
    (P : Set Z) (hL : f '' K = L) (hP : g '' L = P) (hgf : (g.comp f) '' K = P)
    (p : ℕ) (a : Cohomology K p) :
    extension g hg L hLc P hP p (extension f hf K hK L hL p a) =
      extension (g.comp f) (hg.comp hf) K hK P hgf p a := by
  apply (restrictionEquiv (g.comp f) (hg.comp hf) K hK P hgf p).injective
  rw [restriction_comp f hf g hg K hK L hLc P hL hP hgf p,
    restriction_extension, restriction_extension, restriction_extension]

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenEmbeddingSupport

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenEmbeddingSupport

open SingularCohomologyFree NoExoticSixSphere
open IntegralSupportedCohomology (Cohomology)

variable {X : Type} [TopologicalSpace X]

theorem restrictionMap_id (K : Set X) (hK : (ContinuousMap.id X) '' K = K) :
    restrictionMap (ContinuousMap.id X) Topology.IsOpenEmbedding.id K K hK =
      𝟙 (IntegralSupportedCohomology.complex K) := by
  change dualMap (RelativeSingularHomology.mapChain (ContinuousMap.id X) _) = _
  rw [RelativeSingularHomology.mapChain_id, dualMap_id]
  rfl

variable [T2Space X]

theorem extension_id (K : Set X) (hK : IsCompact K)
    (he : (ContinuousMap.id X) '' K = K) (p : ℕ) (a : Cohomology K p) :
    extension (ContinuousMap.id X) Topology.IsOpenEmbedding.id K hK K he p a = a := by
  have hr (b : Cohomology K p) :
      restrictionEquiv (ContinuousMap.id X) Topology.IsOpenEmbedding.id K hK K he p b = b := by
    change (HomologicalComplex.homologyMap (restrictionMap (ContinuousMap.id X)
      Topology.IsOpenEmbedding.id K K he) p).hom b = b
    rw [restrictionMap_id, HomologicalComplex.homologyMap_id]
    rfl
  exact (hr _).symm.trans
    (restriction_extension (ContinuousMap.id X) Topology.IsOpenEmbedding.id K hK K he p a)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenEmbeddingSupport
