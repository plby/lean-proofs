import Wikipedia.NoExoticSixSphere.SupportedModTwoExcision

/-!
# Extension from an actual compact support in an open subspace

The original pair restriction to an open subspace is an excision
isomorphism on cohomology with compact support. Its inverse defines
extension to the same support viewed in the ambient space. This
extension commutes with the original support-enlargement maps.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.OpenSupportCohomology

open SupportedModTwoCohomology (Cohomology extend extendCochain)

variable {X : Type} [TopologicalSpace X] (U : Set X)

abbrev imageSupport (K : Set U) : Set X := Subtype.val '' K

theorem inclusion_mapsTo (K : Set U) :
    Set.MapsTo (subtypeInclusion U) Kᶜ (imageSupport U K)ᶜ := by
  rintro x hx ⟨y, hy, he⟩
  exact hx (Subtype.val_injective he ▸ hy)

/-- The actual cochain restriction induced by inclusion of the pairs. -/
def restrictionMap (K : Set U) :
    SupportedModTwoCohomology.complex (imageSupport U K) ⟶
      SupportedModTwoCohomology.complex K :=
  RelativeModTwoCochains.pullbackMap (subtypeInclusion U) (inclusion_mapsTo U K)

/-- The actual pair restriction commutes with enlargement of support on original cochains. -/
theorem restrictionMap_extend {K L : Set U} (h : K ⊆ L) :
    extendCochain (Set.image_mono h) ≫ restrictionMap U L =
      restrictionMap U K ≫ extendCochain h := by
  change ModTwoDualComplex.map (SupportedRelativeHomology.restrictChain
      (ModuleCat.of ℤ ℤ) (Set.image_mono h)) ≫
      ModTwoDualComplex.map (RelativeCoefficients.mapChain (ModuleCat.of ℤ ℤ)
        (subtypeInclusion U) (inclusion_mapsTo U L)) =
    ModTwoDualComplex.map (RelativeCoefficients.mapChain (ModuleCat.of ℤ ℤ)
      (subtypeInclusion U) (inclusion_mapsTo U K)) ≫
      ModTwoDualComplex.map (SupportedRelativeHomology.restrictChain (ModuleCat.of ℤ ℤ) h)
  rw [← ModTwoDualComplex.map_comp, ← ModTwoDualComplex.map_comp]
  apply congrArg ModTwoDualComplex.map
  change RelativeCoefficients.mapChain _ (subtypeInclusion U) _ ≫
      RelativeCoefficients.mapChain _ (ContinuousMap.id X) _ =
    RelativeCoefficients.mapChain _ (ContinuousMap.id U) _ ≫
      RelativeCoefficients.mapChain _ (subtypeInclusion U) _
  rw [← RelativeCoefficients.mapChain_comp, ← RelativeCoefficients.mapChain_comp]
  rfl

theorem restriction_extend {K L : Set U} (h : K ⊆ L) (p : ℕ)
    (a : Cohomology (imageSupport U K) p) :
    (HomologicalComplex.homologyMap (restrictionMap U L) p).hom (extend (Set.image_mono h) p a) =
      extend h p ((HomologicalComplex.homologyMap (restrictionMap U K) p).hom a) := by
  have he := congrArg (fun f => HomologicalComplex.homologyMap f p) (restrictionMap_extend U h)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  exact congrArg (fun f => f.hom a) he

variable [T2Space X]

/-- The original restriction is a quasi-isomorphism for a compact support in an open subspace. -/
theorem restrictionMap_quasiIso (hU : IsOpen U) (K : Set U) (hK : IsCompact K) :
    QuasiIso (restrictionMap U K) := by
  have hgen (L : Set U) (hL : L = Subtype.val ⁻¹' (imageSupport U K)ᶜ)
      (hf : Set.MapsTo (subtypeInclusion U) L (imageSupport U K)ᶜ) :
      QuasiIso (RelativeModTwoCochains.pullbackMap (subtypeInclusion U) hf) := by
    subst L
    exact RelativeModTwoCochains.excisionPullbackMap_quasiIso U (imageSupport U K)ᶜ hU
      (hK.image continuous_subtype_val).isClosed.isOpen_compl
      (SupportedModTwoCohomology.neighborhood_complement_cover U (imageSupport U K)
        (by rintro _ ⟨x, _, rfl⟩; exact x.property))
  exact hgen Kᶜ (by rw [Set.preimage_compl, Set.preimage_image_eq K Subtype.val_injective])
    (inclusion_mapsTo U K)

/-- Excision with the actual neighborhood support, retaining its original restriction map. -/
def restrictionEquiv (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (p : ℕ) :
    Cohomology (imageSupport U K) p ≃ₗ[ℤ] Cohomology K p := by
  let := restrictionMap_quasiIso U hU K hK
  exact (isoOfQuasiIsoAt (restrictionMap U K) p).toLinearEquiv

theorem restrictionEquiv_toLinearMap (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (p : ℕ) :
    (restrictionEquiv U hU K hK p).toLinearMap =
      (HomologicalComplex.homologyMap (restrictionMap U K) p).hom := rfl

/-- Extension to the original image support is the inverse of actual cohomological excision. -/
def extension (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (p : ℕ) :
    Cohomology K p →ₗ[ℤ] Cohomology (imageSupport U K) p :=
  (restrictionEquiv U hU K hK p).symm.toLinearMap

theorem restriction_extension (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (p : ℕ)
    (a : Cohomology K p) :
    restrictionEquiv U hU K hK p (extension U hU K hK p a) = a :=
  (restrictionEquiv U hU K hK p).apply_symm_apply a

theorem extension_restriction (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (p : ℕ)
    (a : Cohomology (imageSupport U K) p) :
    extension U hU K hK p (restrictionEquiv U hU K hK p a) = a :=
  (restrictionEquiv U hU K hK p).symm_apply_apply a

/-- Actual extension from the open subspace commutes with both original support maps. -/
theorem extension_extend (hU : IsOpen U) {K L : Set U} (h : K ⊆ L)
    (hK : IsCompact K) (hL : IsCompact L) (p : ℕ) (a : Cohomology K p) :
    extend (Set.image_mono h) p (extension U hU K hK p a) =
      extension U hU L hL p (extend h p a) := by
  apply (restrictionEquiv U hU L hL p).injective
  exact (restriction_extend U h p (extension U hU K hK p a)).trans
    ((congrArg (extend h p) (restriction_extension U hU K hK p a)).trans
      (restriction_extension U hU L hL p (extend h p a)).symm)

end NoExoticSixSphere.OpenSupportCohomology
