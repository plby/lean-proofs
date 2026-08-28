import Wikipedia.NoExoticSixSphere.OpenSupportCohomology
import Wikipedia.NoExoticSixSphere.RelativeCoefficientHomeomorph

/-!
# Compact-support extension along actual open embeddings

Restriction along an open embedding factors through its homeomorphism
onto its open image and original relative excision. Its inverse extends
cohomology from each compact support to its actual image support.
The support may be named separately, so composition does not replace
the original maps by noncanonical identifications of groups.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.OpenEmbeddingSupportCohomology

open SupportedModTwoCohomology (Cohomology extend extendCochain)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)

include hf

theorem mapsTo_compl (K : Set X) (L : Set Y) (hL : f '' K = L) :
    Set.MapsTo f Kᶜ Lᶜ := by
  subst L
  rintro x hx ⟨y, hy, he⟩
  exact hx (hf.injective he ▸ hy)

/-- Restriction by the original map of pairs with this actual image support. -/
def restrictionMap (K : Set X) (L : Set Y) (hL : f '' K = L) :
    SupportedModTwoCohomology.complex L ⟶ SupportedModTwoCohomology.complex K :=
  RelativeModTwoCochains.pullbackMap f (mapsTo_compl f hf K L hL)

/-- Both actual support maps commute with the original pair restriction. -/
theorem restrictionMap_extend {K N : Set X} {L P : Set Y} (hKN : K ⊆ N) (hLP : L ⊆ P)
    (hL : f '' K = L) (hP : f '' N = P) :
    extendCochain hLP ≫ restrictionMap f hf N P hP =
      restrictionMap f hf K L hL ≫ extendCochain hKN := by
  change ModTwoDualComplex.map _ ≫ ModTwoDualComplex.map _ =
    ModTwoDualComplex.map _ ≫ ModTwoDualComplex.map _
  rw [← ModTwoDualComplex.map_comp, ← ModTwoDualComplex.map_comp]
  apply congrArg ModTwoDualComplex.map
  change RelativeCoefficients.mapChain _ f _ ≫
      RelativeCoefficients.mapChain _ (ContinuousMap.id Y) _ =
    RelativeCoefficients.mapChain _ (ContinuousMap.id X) _ ≫
      RelativeCoefficients.mapChain _ f _
  rw [← RelativeCoefficients.mapChain_comp, ← RelativeCoefficients.mapChain_comp]
  rfl

variable [T2Space Y]

/-- Open-image excision proves that the original restriction is a quasi-isomorphism. -/
theorem restrictionMap_quasiIso (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) : QuasiIso (restrictionMap f hf K L hL) := by
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
    refine ⟨e.symm y, hyK, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply y)
  let i := ModTwoDualComplex.mapIso
    (RelativeCoefficients.homeomorphChainIso (ModuleCat.of ℤ ℤ) e he hei)
  let r := RelativeModTwoCochains.excisionPullbackMap (Set.range f) (f '' K)ᶜ
  have hi : restrictionMap f hf K (f '' K) rfl = r ≫ i.hom := by
    change ModTwoDualComplex.map _ = ModTwoDualComplex.map _ ≫
      ModTwoDualComplex.map (RelativeCoefficients.mapChain (ModuleCat.of ℤ ℤ)
        (e : C(X, Set.range f)) he)
    rw [← ModTwoDualComplex.map_comp, ← RelativeCoefficients.mapChain_comp]
    rfl
  let : QuasiIso r := RelativeModTwoCochains.excisionPullbackMap_quasiIso
    (Set.range f) (f '' K)ᶜ hf.isOpen_range (hK.image f.continuous).isClosed.isOpen_compl
    (SupportedModTwoCohomology.neighborhood_complement_cover (Set.range f) (f '' K)
      (Set.image_subset_range _ _))
  rw [hi]
  infer_instance

/-- The forward map is actual restriction along the supplied open embedding. -/
def restrictionEquiv (K : Set X) (hK : IsCompact K) (L : Set Y)
    (hL : f '' K = L) (p : ℕ) : Cohomology L p ≃ₗ[ℤ] Cohomology K p := by
  let := restrictionMap_quasiIso f hf K hK L hL
  exact (isoOfQuasiIsoAt (restrictionMap f hf K L hL) p).toLinearEquiv

theorem restrictionEquiv_toLinearMap (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) (p : ℕ) :
    (restrictionEquiv f hf K hK L hL p).toLinearMap =
      (HomologicalComplex.homologyMap (restrictionMap f hf K L hL) p).hom := rfl

/-- Extend to the actual image support using inverse original restriction. -/
def extension (K : Set X) (hK : IsCompact K) (L : Set Y) (hL : f '' K = L) (p : ℕ) :
    Cohomology K p →ₗ[ℤ] Cohomology L p :=
  (restrictionEquiv f hf K hK L hL p).symm.toLinearMap

theorem restriction_extension (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) (p : ℕ) (a : Cohomology K p) :
    restrictionEquiv f hf K hK L hL p (extension f hf K hK L hL p a) = a :=
  (restrictionEquiv f hf K hK L hL p).apply_symm_apply a

theorem extension_restriction (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) (p : ℕ) (a : Cohomology L p) :
    extension f hf K hK L hL p (restrictionEquiv f hf K hK L hL p a) = a :=
  (restrictionEquiv f hf K hK L hL p).symm_apply_apply a

/-- The actual inverse excision maps commute with both support transitions. -/
theorem extension_extend {K N : Set X} {L P : Set Y} (hKN : K ⊆ N) (hLP : L ⊆ P)
    (hK : IsCompact K) (hN : IsCompact N) (hL : f '' K = L) (hP : f '' N = P)
    (p : ℕ) (a : Cohomology K p) :
    extend hLP p (extension f hf K hK L hL p a) =
      extension f hf N hN P hP p (extend hKN p a) := by
  apply (restrictionEquiv f hf N hN P hP p).injective
  have he := congrArg (fun m => HomologicalComplex.homologyMap m p)
    (restrictionMap_extend f hf hKN hLP hL hP)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  have he' := congrArg (fun m => m.hom (extension f hf K hK L hL p a)) he
  exact he'.trans ((congrArg (extend hKN p) (restriction_extension f hf K hK L hL p a)).trans
    (restriction_extension f hf N hN P hP p (extend hKN p a)).symm)

end NoExoticSixSphere.OpenEmbeddingSupportCohomology
