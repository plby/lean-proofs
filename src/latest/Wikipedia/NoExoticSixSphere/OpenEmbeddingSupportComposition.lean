import Wikipedia.NoExoticSixSphere.OpenEmbeddingSupportCohomology

/-!
# Composition of actual open-embedding support extensions

The original pair pullbacks compose on cochains. Passing to genuine
cohomology and inverting the proved excision equivalences gives
composition for compact-support extension, with separately named
intermediate and final image supports.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.OpenEmbeddingSupportCohomology

open SupportedModTwoCohomology (Cohomology)

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)
  (g : C(Y, Z)) (hg : Topology.IsOpenEmbedding g)

/-- Composition is the original contravariant pair-map identity on actual cochains. -/
theorem restrictionMap_comp (K : Set X) (L : Set Y) (P : Set Z)
    (hL : f '' K = L) (hP : g '' L = P) (hgf : (g.comp f) '' K = P) :
    restrictionMap (g.comp f) (hg.comp hf) K P hgf =
      restrictionMap g hg L P hP ≫ restrictionMap f hf K L hL := by
  change ModTwoDualComplex.map _ = ModTwoDualComplex.map _ ≫ ModTwoDualComplex.map _
  rw [← ModTwoDualComplex.map_comp, ← RelativeCoefficients.mapChain_comp]

variable [T2Space Y] [T2Space Z]

/-- The excision equivalences retain the original composite restriction on cohomology. -/
theorem restriction_comp (K : Set X) (hK : IsCompact K) (L : Set Y) (hLc : IsCompact L)
    (P : Set Z) (hL : f '' K = L) (hP : g '' L = P) (hgf : (g.comp f) '' K = P)
    (p : ℕ) (a : Cohomology P p) :
    restrictionEquiv (g.comp f) (hg.comp hf) K hK P hgf p a =
      restrictionEquiv f hf K hK L hL p (restrictionEquiv g hg L hLc P hP p a) := by
  have he := congrArg (fun m => HomologicalComplex.homologyMap m p)
    (restrictionMap_comp f hf g hg K L P hL hP hgf)
  rw [HomologicalComplex.homologyMap_comp] at he
  exact congrArg (fun m => m.hom a) he

/-- Extension along a composite is successive extension along the two actual open embeddings. -/
theorem extension_comp (K : Set X) (hK : IsCompact K) (L : Set Y) (hLc : IsCompact L)
    (P : Set Z) (hL : f '' K = L) (hP : g '' L = P) (hgf : (g.comp f) '' K = P)
    (p : ℕ) (a : Cohomology K p) :
    extension g hg L hLc P hP p (extension f hf K hK L hL p a) =
      extension (g.comp f) (hg.comp hf) K hK P hgf p a := by
  apply (restrictionEquiv (g.comp f) (hg.comp hf) K hK P hgf p).injective
  rw [restriction_comp f hf g hg K hK L hLc P hL hP hgf p,
    restriction_extension, restriction_extension, restriction_extension]

end NoExoticSixSphere.OpenEmbeddingSupportCohomology

namespace NoExoticSixSphere.OpenEmbeddingSupportCohomology

open SupportedModTwoCohomology (Cohomology)

variable {X : Type} [TopologicalSpace X]

/-- Original pair restriction along the identity is the identity cochain map. -/
theorem restrictionMap_id (K : Set X) (hK : (ContinuousMap.id X) '' K = K) :
    restrictionMap (ContinuousMap.id X) Topology.IsOpenEmbedding.id K K hK =
      𝟙 (SupportedModTwoCohomology.complex K) := by
  change ModTwoDualComplex.map (RelativeCoefficients.mapChain _ (ContinuousMap.id X) _) = _
  rw [RelativeCoefficients.mapChain_id, ModTwoDualComplex.map_id]

variable [T2Space X]

/-- Inverse excision along the identity leaves every actual support class unchanged. -/
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

end NoExoticSixSphere.OpenEmbeddingSupportCohomology
