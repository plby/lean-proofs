import Wikipedia.HopfProblem.DegreeCollapseIntegralSupportChartTransport

/-!
# Integral homology of actual compact supports in an open subspace

The support in the ambient space is its actual image under subtype
inclusion. Integral excision makes this original pair inclusion an
equivalence on homology. Both support restriction and point evaluation
commute with the original inclusion maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenSupport

open SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)

abbrev imageSupport (K : Set U) : Set X := Subtype.val '' K

theorem inclusion_mapsTo (K : Set U) :
    Set.MapsTo (subtypeInclusion U) Kᶜ (imageSupport U K)ᶜ := by
  rintro x hx ⟨y, hy, he⟩
  exact hx (Subtype.val_injective he ▸ hy)

/-- The original pair inclusion on integral chain complexes. -/
def inclusionChain (K : Set U) :
    Complex (ModuleCat.of ℤ ℤ) K ⟶ Complex (ModuleCat.of ℤ ℤ) (imageSupport U K) :=
  RelativeCoefficients.mapChain (ModuleCat.of ℤ ℤ) (subtypeInclusion U) (inclusion_mapsTo U K)

abbrev inclusionMap (K : Set U) (n : ℕ) :
    Homology (ModuleCat.of ℤ ℤ) K n →ₗ[ℤ] Homology (ModuleCat.of ℤ ℤ) (imageSupport U K) n :=
  homologyLinearMap (inclusionChain U K) n

theorem inclusionChain_restrict {K L : Set U} (h : K ⊆ L) :
    inclusionChain U L ≫ restrictChain (ModuleCat.of ℤ ℤ) (Set.image_mono h) =
      restrictChain (ModuleCat.of ℤ ℤ) h ≫ inclusionChain U K := by
  change RelativeCoefficients.mapChain _ (subtypeInclusion U) _ ≫
      RelativeCoefficients.mapChain _ (ContinuousMap.id X) _ =
    RelativeCoefficients.mapChain _ (ContinuousMap.id U) _ ≫
      RelativeCoefficients.mapChain _ (subtypeInclusion U) _
  rw [← RelativeCoefficients.mapChain_comp, ← RelativeCoefficients.mapChain_comp]
  rfl

/-- The exact restriction square on original integral homology. -/
theorem inclusionMap_restrict {K L : Set U} (h : K ⊆ L) (n : ℕ)
    (a : Homology (ModuleCat.of ℤ ℤ) L n) :
    restrict (ModuleCat.of ℤ ℤ) (Set.image_mono h) n (inclusionMap U L n a) =
      inclusionMap U K n (restrict (ModuleCat.of ℤ ℤ) h n a) := by
  have he := congrArg (fun f => homologyLinearMap f n) (inclusionChain_restrict U h)
  simp only [homologyLinearMap_comp] at he
  exact LinearMap.congr_fun he a

theorem inclusion_evaluation_chain (K : Set U) (x : U) (hx : x ∈ K) :
    inclusionChain U K ≫ restrictChain (ModuleCat.of ℤ ℤ)
        (show {(x : X)} ⊆ imageSupport U K from Set.singleton_subset_iff.mpr ⟨x, hx, rfl⟩) =
      restrictChain (ModuleCat.of ℤ ℤ) (Set.singleton_subset_iff.mpr hx) ≫
        RelativeSingularHomology.neighborhoodChainMap U x := by
  have hi := inclusion_mapsTo U K
  have ho : Set.MapsTo (ContinuousMap.id X) (imageSupport U K)ᶜ ({(x : X)}ᶜ : Set X) := by
    intro y hy he
    change y = (x : X) at he
    subst y
    exact hy ⟨x, hx, rfl⟩
  have hu : Set.MapsTo (ContinuousMap.id U) Kᶜ ({x}ᶜ : Set U) := by
    intro y hy he
    change y = x at he
    subst y
    exact hy hx
  change RelativeSingularHomology.mapChain (subtypeInclusion U) hi ≫
      RelativeSingularHomology.mapChain (ContinuousMap.id X) ho =
    RelativeSingularHomology.mapChain (ContinuousMap.id U) hu ≫
      RelativeSingularHomology.mapChain (subtypeInclusion U)
        (RelativeSingularHomology.inclusion_mapsTo_puncture U x)
  rw [← RelativeSingularHomology.mapChain_comp, ← RelativeSingularHomology.mapChain_comp]
  rfl

/-- The original ambient evaluation is the included original local evaluation. -/
theorem evaluate_inclusion (K : Set U) (x : U) (hx : x ∈ K) (n : ℕ) :
    (evaluate (ModuleCat.of ℤ ℤ) (imageSupport U K) (x : X) ⟨x, hx, rfl⟩ n).comp
        (inclusionMap U K n) =
      (RelativeSingularHomology.neighborhoodMap U x n).comp
        (evaluate (ModuleCat.of ℤ ℤ) K x hx n) := by
  let l := restrictChain (ModuleCat.of ℤ ℤ)
    (show {(x : X)} ⊆ imageSupport U K from Set.singleton_subset_iff.mpr ⟨x, hx, rfl⟩)
  let r := restrictChain (ModuleCat.of ℤ ℤ) (Set.singleton_subset_iff.mpr hx)
  exact (homologyLinearMap_comp (inclusionChain U K) l n).symm.trans
    ((congrArg (fun k => homologyLinearMap k n) (inclusion_evaluation_chain U K x hx)).trans
      (homologyLinearMap_comp r (RelativeSingularHomology.neighborhoodChainMap U x) n))

variable [T2Space X]

/-- Integral excision for the actual image of a compact support in an open subspace. -/
theorem inclusionChain_quasiIso (hU : IsOpen U) (K : Set U) (hK : IsCompact K) :
    QuasiIso (inclusionChain U K) := by
  have hgen (L : Set U) (hL : L = Subtype.val ⁻¹' (imageSupport U K)ᶜ)
      (hf : Set.MapsTo (subtypeInclusion U) L (imageSupport U K)ᶜ) :
      QuasiIso (RelativeCoefficients.mapChain (ModuleCat.of ℤ ℤ) (subtypeInclusion U) hf) := by
    subst L
    exact RelativeSingularHomology.excisionChainMap_quasiIso U (imageSupport U K)ᶜ hU
      (hK.image continuous_subtype_val).isClosed.isOpen_compl
      (support_complement_cover U (imageSupport U K)
        (by rintro _ ⟨x, _, rfl⟩; exact x.property))
  exact hgen Kᶜ (by rw [Set.preimage_compl, Set.preimage_image_eq K Subtype.val_injective])
    (inclusion_mapsTo U K)

/-- The original inclusion-induced integral homology equivalence. -/
def inclusionEquiv (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (n : ℕ) :
    Homology (ModuleCat.of ℤ ℤ) K n ≃ₗ[ℤ] Homology (ModuleCat.of ℤ ℤ) (imageSupport U K) n := by
  let := inclusionChain_quasiIso U hU K hK
  exact (isoOfQuasiIsoAt (inclusionChain U K) n).toLinearEquiv

theorem inclusionEquiv_toLinearMap (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (n : ℕ) :
    (inclusionEquiv U hU K hK n).toLinearMap = inclusionMap U K n := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenSupport
