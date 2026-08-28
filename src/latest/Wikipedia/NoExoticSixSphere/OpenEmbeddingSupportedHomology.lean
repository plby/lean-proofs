import Wikipedia.NoExoticSixSphere.OpenEmbeddingSupportCohomology
import Wikipedia.NoExoticSixSphere.CompactSupportedCapInclusion

/-!
# Actual supported homology under open embeddings

The original pair map factors as a pair homeomorphism onto the open
image followed by the original excision inclusion. The resulting local
isomorphism preserves the unique nonzero mod-two local class. The
original evaluation square then proves preservation of the constructed
compact-supported fundamental class, without changing either atlas.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.OpenEmbeddingSupportedHomology

open SupportedRelativeHomology
open OpenEmbeddingSupportCohomology (mapsTo_compl)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)

/-- The original map of pairs for an actual image support. -/
def mapChain (A : ModuleCat.{0} ℤ) (K : Set X) (L : Set Y) (hL : f '' K = L) :
    Complex A K ⟶ Complex A L :=
  RelativeCoefficients.mapChain A f (mapsTo_compl f hf K L hL)

/-- The actual induced map, retaining the original relative coefficient complexes. -/
abbrev map (A : ModuleCat.{0} ℤ) (K : Set X) (L : Set Y) (hL : f '' K = L) (k : ℕ) :
    Homology A K k →ₗ[ℤ] Homology A L k :=
  homologyLinearMap (mapChain f hf A K L hL) k

variable [T2Space Y]

/-- Open-image factorization and actual excision prove the original map is a quasi-isomorphism. -/
theorem mapChain_quasiIso (p : ℕ) (hp : p ≠ 0) (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) :
    QuasiIso (mapChain f hf (ModuleCat.of ℤ (ZMod p)) K L hL) := by
  subst L
  let e : X ≃ₜ Set.range f := hf.isEmbedding.toHomeomorph
  let S := RelativeSingularHomology.overlapIn (Set.range f) (f '' K)ᶜ
  have he : Set.MapsTo e Kᶜ S := by
    intro x hx
    change f x ∉ f '' K
    exact mapsTo_compl f hf K (f '' K) rfl hx
  have hei : Set.MapsTo e.symm S Kᶜ := by
    intro y hy hyK
    apply hy
    exact ⟨e.symm y, hyK, congrArg Subtype.val (e.apply_symm_apply y)⟩
  let i := RelativeCoefficients.homeomorphChainIso (ModuleCat.of ℤ (ZMod p)) e he hei
  let j := RelativeCoefficients.modExcisionChainMap p (Set.range f) (f '' K)ᶜ
  have hj : mapChain f hf (ModuleCat.of ℤ (ZMod p)) K (f '' K) rfl = i.hom ≫ j := by
    change RelativeCoefficients.mapChain _ f _ =
      RelativeCoefficients.mapChain _ (e : C(X, Set.range f)) he ≫
        RelativeCoefficients.mapChain _ (subtypeInclusion (Set.range f)) _
    rw [← RelativeCoefficients.mapChain_comp]
    rfl
  let : QuasiIso j := RelativeCoefficients.modExcisionChainMap_quasiIso p hp
    (Set.range f) (f '' K)ᶜ hf.isOpen_range (hK.image f.continuous).isClosed.isOpen_compl
    (support_complement_cover (Set.range f) (f '' K) (Set.image_subset_range _ _))
  rw [hj]
  infer_instance

/-- The equivalence has the original pair-induced map as its forward map. -/
def mapEquiv (p : ℕ) (hp : p ≠ 0) (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) (k : ℕ) :
    Homology (ModuleCat.of ℤ (ZMod p)) K k ≃ₗ[ℤ] Homology (ModuleCat.of ℤ (ZMod p)) L k := by
  let := mapChain_quasiIso f hf p hp K hK L hL
  exact (isoOfQuasiIsoAt (mapChain f hf (ModuleCat.of ℤ (ZMod p)) K L hL) k).toLinearEquiv

theorem mapEquiv_toLinearMap (p : ℕ) (hp : p ≠ 0) (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) (k : ℕ) :
    (mapEquiv f hf p hp K hK L hL k).toLinearMap =
      map f hf (ModuleCat.of ℤ (ZMod p)) K L hL k := rfl

omit [T2Space Y] in
/-- Evaluation commutes with the original support map already on the relative complexes. -/
theorem evaluate_map_chain (A : ModuleCat.{0} ℤ) (K : Set X) (L : Set Y)
    (hL : f '' K = L) (x : X) (hx : x ∈ K) :
    mapChain f hf A K L hL ≫
        restrictChain A (Set.singleton_subset_iff.mpr (hL ▸ Set.mem_image_of_mem f hx)) =
      restrictChain A (Set.singleton_subset_iff.mpr hx) ≫
        mapChain f hf A {x} {f x} Set.image_singleton := by
  change RelativeCoefficients.mapChain _ f _ ≫
      RelativeCoefficients.mapChain _ (ContinuousMap.id Y) _ =
    RelativeCoefficients.mapChain _ (ContinuousMap.id X) _ ≫
      RelativeCoefficients.mapChain _ f _
  rw [← RelativeCoefficients.mapChain_comp, ← RelativeCoefficients.mapChain_comp]
  rfl

omit [T2Space Y] in
/-- The actual local evaluation square on supported homology. -/
theorem evaluate_map (A : ModuleCat.{0} ℤ) (K : Set X) (L : Set Y)
    (hL : f '' K = L) (x : X) (hx : x ∈ K) (k : ℕ) :
    (evaluate A L (f x) (hL ▸ Set.mem_image_of_mem f hx) k).comp (map f hf A K L hL k) =
      (map f hf A {x} {f x} Set.image_singleton k).comp (evaluate A K x hx k) := by
  have he := congrArg (fun m => homologyLinearMap m k) (evaluate_map_chain f hf A K L hL x hx)
  simp only [homologyLinearMap_comp] at he
  exact he

end NoExoticSixSphere.OpenEmbeddingSupportedHomology

namespace NoExoticSixSphere.CompactSupportedFundamentalClass

open SupportedRelativeHomology OpenEmbeddingSupportedHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
  [ChartedSpace E X] [ChartedSpace E Y]
  (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)

/-- The original open-embedding pair map preserves the constructed fundamental classes. -/
theorem openEmbedding_fundamentalClass (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) :
    map f hf (ModuleCat.of ℤ (ZMod 2)) K L hL (n + 3)
        (fundamentalClass (E := E) n K hK) =
      fundamentalClass (E := E) n L (hL ▸ hK.image f.continuous) := by
  apply unique (E := E) n L (hL ▸ hK.image f.continuous)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hL.symm ▸ hy
  apply (LinearMap.congr_fun (evaluate_map f hf (ModuleCat.of ℤ (ZMod 2)) K L hL x hx
    (n + 3)) (fundamentalClass (E := E) n K hK)).trans
  apply (congrArg (map f hf (ModuleCat.of ℤ (ZMod 2)) {x} {f x}
    Set.image_singleton (n + 3)) (isFundamentalOn (E := E) n K hK x hx)).trans
  exact ModTwoLocalClass.injective_map_manifoldClass (E := E) n x (f x)
    (map f hf (ModuleCat.of ℤ (ZMod 2)) {x} {f x} Set.image_singleton (n + 3))
    (mapEquiv f hf 2 (by decide) {x} isCompact_singleton {f x} Set.image_singleton
      (n + 3)).injective

end NoExoticSixSphere.CompactSupportedFundamentalClass
