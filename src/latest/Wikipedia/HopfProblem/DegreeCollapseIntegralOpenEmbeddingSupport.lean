import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenSupportCohomology
import Wikipedia.NoExoticSixSphere.RelativeCoefficientHomeomorph

/-!
# Integral support transport by actual open embeddings

The original pair map factors through the homeomorphism onto its open
image and genuine integral excision. Freeness of the actual relative
chain terms then makes its original integral cochain dual a
quasi-isomorphism. Inverse restriction extends to the actual compact
image support, with exact support-transition compatibility.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenEmbeddingSupport

open SingularMayerVietoris SingularCohomologyFree NoExoticSixSphere
open SupportedRelativeHomology
open IntegralSupportedCohomology (Cohomology extend extendCochain)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)

include hf in
theorem mapsTo_compl (K : Set X) (L : Set Y) (hL : f '' K = L) :
    Set.MapsTo f Kᶜ Lᶜ := by
  subst L
  rintro x hx ⟨y, hy, he⟩
  exact hx (hf.injective he ▸ hy)

/-- The original integral map of pairs on the actual image support. -/
def mapChain (K : Set X) (L : Set Y) (hL : f '' K = L) :
    Complex (ModuleCat.of ℤ ℤ) K ⟶ Complex (ModuleCat.of ℤ ℤ) L :=
  RelativeSingularHomology.mapChain f (mapsTo_compl f hf K L hL)

abbrev map (K : Set X) (L : Set Y) (hL : f '' K = L) (k : ℕ) :
    Homology (ModuleCat.of ℤ ℤ) K k →ₗ[ℤ] Homology (ModuleCat.of ℤ ℤ) L k :=
  homologyLinearMap (mapChain f hf K L hL) k

theorem mapChain_restrict {K N : Set X} {L P : Set Y}
    (hKN : K ⊆ N) (hLP : L ⊆ P) (hL : f '' K = L) (hP : f '' N = P) :
    mapChain f hf N P hP ≫ restrictChain (ModuleCat.of ℤ ℤ) hLP =
      restrictChain (ModuleCat.of ℤ ℤ) hKN ≫ mapChain f hf K L hL := by
  change RelativeSingularHomology.mapChain f _ ≫
      RelativeSingularHomology.mapChain (ContinuousMap.id Y)
        (show Set.MapsTo (ContinuousMap.id Y) Pᶜ Lᶜ from fun _ hx hy => hx (hLP hy)) =
    RelativeSingularHomology.mapChain (ContinuousMap.id X)
        (show Set.MapsTo (ContinuousMap.id X) Nᶜ Kᶜ from fun _ hx hy => hx (hKN hy)) ≫
      RelativeSingularHomology.mapChain f _
  rw [← RelativeSingularHomology.mapChain_comp, ← RelativeSingularHomology.mapChain_comp]
  rfl

/-- Actual restriction is the integral cochain dual of that same pair map. -/
def restrictionMap (K : Set X) (L : Set Y) (hL : f '' K = L) :
    IntegralSupportedCohomology.complex L ⟶ IntegralSupportedCohomology.complex K :=
  dualMap (mapChain f hf K L hL)

theorem restrictionMap_extend {K N : Set X} {L P : Set Y}
    (hKN : K ⊆ N) (hLP : L ⊆ P) (hL : f '' K = L) (hP : f '' N = P) :
    extendCochain hLP ≫ restrictionMap f hf N P hP =
      restrictionMap f hf K L hL ≫ extendCochain hKN := by
  exact (dualMap_comp (mapChain f hf N P hP)
    (restrictChain (ModuleCat.of ℤ ℤ) hLP)).symm.trans
      ((congrArg dualMap (mapChain_restrict f hf hKN hLP hL hP)).trans
        (dualMap_comp (restrictChain (ModuleCat.of ℤ ℤ) hKN) (mapChain f hf K L hL)))

variable [T2Space Y]

/-- The original chain map is integral excision after an actual pair homeomorphism. -/
theorem mapChain_quasiIso (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) : QuasiIso (mapChain f hf K L hL) := by
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
  let i := RelativeCoefficients.homeomorphChainIso (ModuleCat.of ℤ ℤ) e he hei
  let j := RelativeSingularHomology.excisionChainMap (Set.range f) (f '' K)ᶜ
  have hj : mapChain f hf K (f '' K) rfl = i.hom ≫ j := by
    change RelativeSingularHomology.mapChain f _ =
      RelativeSingularHomology.mapChain (e : C(X, Set.range f)) he ≫
        RelativeSingularHomology.mapChain (subtypeInclusion (Set.range f)) _
    rw [← RelativeSingularHomology.mapChain_comp]
    rfl
  have hjq : QuasiIso j := RelativeSingularHomology.excisionChainMap_quasiIso
    (Set.range f) (f '' K)ᶜ hf.isOpen_range (hK.image f.continuous).isClosed.isOpen_compl
    (support_complement_cover (Set.range f) (f '' K) (Set.image_subset_range _ _))
  have hiq : QuasiIso i.hom := inferInstance
  rw [hj]
  exact quasiIso_comp i.hom j (hφ := hiq) (hφ' := hjq)

def mapEquiv (K : Set X) (hK : IsCompact K) (L : Set Y)
    (hL : f '' K = L) (k : ℕ) :
    Homology (ModuleCat.of ℤ ℤ) K k ≃ₗ[ℤ] Homology (ModuleCat.of ℤ ℤ) L k := by
  let := mapChain_quasiIso f hf K hK L hL
  exact (isoOfQuasiIsoAt (mapChain f hf K L hL) k).toLinearEquiv

theorem mapEquiv_toLinearMap (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) (k : ℕ) :
    (mapEquiv f hf K hK L hL k).toLinearMap = map f hf K L hL k := rfl

/-- Dual excision uses projectivity of the actual integral relative chain terms. -/
theorem restrictionMap_quasiIso (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) : QuasiIso (restrictionMap f hf K L hL) := by
  let (k : ℕ) : Projective ((Complex (ModuleCat.of ℤ ℤ) K).X k) := by
    let : Module.Free ℤ ((Complex (ModuleCat.of ℤ ℤ) K).X k) :=
      RelativeSingularHomology.chains_free Kᶜ k
    infer_instance
  let (k : ℕ) : Projective ((Complex (ModuleCat.of ℤ ℤ) L).X k) := by
    let : Module.Free ℤ ((Complex (ModuleCat.of ℤ ℤ) L).X k) :=
      RelativeSingularHomology.chains_free Lᶜ k
    infer_instance
  let := mapChain_quasiIso f hf K hK L hL
  exact IntegralCochainTransport.dualMap_quasiIso_of_projective (mapChain f hf K L hL)

def restrictionEquiv (K : Set X) (hK : IsCompact K) (L : Set Y)
    (hL : f '' K = L) (p : ℕ) : Cohomology L p ≃ₗ[ℤ] Cohomology K p := by
  let := restrictionMap_quasiIso f hf K hK L hL
  exact (isoOfQuasiIsoAt (restrictionMap f hf K L hL) p).toLinearEquiv

theorem restrictionEquiv_toLinearMap (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) (p : ℕ) :
    (restrictionEquiv f hf K hK L hL p).toLinearMap =
      (HomologicalComplex.homologyMap (restrictionMap f hf K L hL) p).hom := rfl

/-- Inverse original restriction extends to the genuine compact image support. -/
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

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenEmbeddingSupport
