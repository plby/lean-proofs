import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportOpenEmbedding
import Wikipedia.NoExoticSixSphere.CompactSupportedCapInclusion

/-!
# Actual integral compact-support representatives inside neighborhoods

Original integral excision restricts a supported class to an actual
open neighborhood of its compact support. The resulting class in the
original directed limit is unchanged by enlarging that support inside
the neighborhood.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

open SingularMayerVietoris NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] [T2Space X] (U : Set X)

def insideCompact (K : Compacts X) (hKU : (K : Set X) ⊆ U) : Compacts U :=
  ⟨Subtype.val ⁻¹' (K : Set X),
    SupportedRelativeHomology.supportIn_isCompact U (K : Set X) K.isCompact hKU⟩

omit [T2Space X] in
theorem image_insideCompact (K : Compacts X) (hKU : (K : Set X) ⊆ U) :
    (subtypeInclusion U) '' (insideCompact U K hKU : Set U) = (K : Set X) := by
  change Subtype.val '' (Subtype.val ⁻¹' (K : Set X) : Set U) = (K : Set X)
  exact Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hKU)

/-- Actual restriction, keeping the support as the given ambient compact subset. -/
def insideEquiv (hU : IsOpen U) (K : Compacts X) (hKU : (K : Set X) ⊆ U) (p : ℕ) :
    Component X p K ≃ₗ[ℤ] Component U p (insideCompact U K hKU) :=
  IntegralOpenEmbeddingSupport.restrictionEquiv (subtypeInclusion U)
    hU.isOpenEmbedding_subtypeVal (insideCompact U K hKU : Set U)
    (insideCompact U K hKU).isCompact (K : Set X) (image_insideCompact U K hKU) p

def neighborhoodOf (hU : IsOpen U) (K : Compacts X) (hKU : (K : Set X) ⊆ U) (p : ℕ) :
    Component X p K →ₗ[ℤ] Cohomology U p :=
  (of U p (insideCompact U K hKU)).comp (insideEquiv U hU K hKU p).toLinearMap

theorem neighborhoodOf_eq_of (hU : IsOpen U) (K : Compacts X) (hKU : (K : Set X) ⊆ U)
    (N : Compacts U) (hN : (subtypeInclusion U) '' (N : Set U) = (K : Set X))
    (p : ℕ) (a : Component X p K) :
    neighborhoodOf U hU K hKU p a = of U p N
      (IntegralOpenEmbeddingSupport.restrictionEquiv (subtypeInclusion U)
        hU.isOpenEmbedding_subtypeVal (N : Set U) N.isCompact (K : Set X) hN p a) := by
  have he : insideCompact U K hKU = N := by
    apply SetLike.coe_injective
    change Subtype.val ⁻¹' (K : Set X) = (N : Set U)
    rw [← hN]
    exact Set.preimage_image_eq (N : Set U) Subtype.val_injective
  subst N
  rfl

theorem insideEquiv_extend (hU : IsOpen U) {K L : Compacts X} (h : K ≤ L)
    (hKU : (K : Set X) ⊆ U) (hLU : (L : Set X) ⊆ U) (p : ℕ) (a : Component X p K) :
    insideEquiv U hU L hLU p (IntegralSupportedCohomology.extend h p a) =
      IntegralSupportedCohomology.extend
        (show (insideCompact U K hKU : Set U) ⊆ insideCompact U L hLU from fun _ hx => h hx)
        p (insideEquiv U hU K hKU p a) := by
  have he := congrArg (fun m => HomologicalComplex.homologyMap m p)
    (IntegralOpenEmbeddingSupport.restrictionMap_extend (subtypeInclusion U)
      hU.isOpenEmbedding_subtypeVal
      (show (insideCompact U K hKU : Set U) ⊆ insideCompact U L hLU from fun _ hx => h hx)
      h (image_insideCompact U K hKU) (image_insideCompact U L hLU))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  exact congrArg (fun m => m.hom a) he

/-- Enlarging the actual support inside this neighborhood preserves its genuine limit class. -/
theorem neighborhoodOf_extend (hU : IsOpen U) {K L : Compacts X} (h : K ≤ L)
    (hKU : (K : Set X) ⊆ U) (hLU : (L : Set X) ⊆ U) (p : ℕ) (a : Component X p K) :
    neighborhoodOf U hU L hLU p (IntegralSupportedCohomology.extend h p a) =
      neighborhoodOf U hU K hKU p a := by
  change of U p (insideCompact U L hLU) (insideEquiv U hU L hLU p
    (IntegralSupportedCohomology.extend h p a)) = _
  rw [insideEquiv_extend U hU h hKU hLU p a]
  exact of_transition U p (K := insideCompact U K hKU) (L := insideCompact U L hLU)
    (show insideCompact U K hKU ≤ insideCompact U L hLU from fun _ hx => h hx)
    (insideEquiv U hU K hKU p a)

theorem neighborhoodOf_extension (hU : IsOpen U) (N : Compacts U) (p : ℕ)
    (a : Component U p N) :
    neighborhoodOf U hU (imageCompact U N) (by rintro _ ⟨x, _, rfl⟩; exact x.property) p
      (IntegralOpenSupport.extension U hU (N : Set U) N.isCompact p a) = of U p N a := by
  apply (neighborhoodOf_eq_of U hU (imageCompact U N) _ N rfl p
    (IntegralOpenSupport.extension U hU (N : Set U) N.isCompact p a)).trans
  exact congrArg (of U p N)
    (IntegralOpenSupport.restriction_extension U hU (N : Set U) N.isCompact p a)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology
