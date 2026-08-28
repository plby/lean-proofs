import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCechMaps
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCohomologyBasic
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassNaturality

/-!
# Genuine Čech classes commute with actual open-embedding restriction

The original exact-functor map on native Ext cohomology, with its original
integer endpoint, sends the original Čech extension class to the class of the
literal restricted cocycle. The proof uses the actual short exact extension,
its exact restriction, and the genuine local-lift comparison.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.EmbeddingCech

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open CuspNormalization.SheafCohomologyFinitePushforward

variable {T X : TopCat.{0}} (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)
  {F : TopCat.Sheaf AddCommGrpCat.{0} X} {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U) (hU : ∀ x : X, ∃ i : ι, x ∈ U i)

/-- The actual native Ext restriction of the original Čech class is the
genuine extension class of its literal inverse-image cocycle. -/
theorem cohomologyMap_classOf :
    Embedding.cohomologyMap f hf F 1 (classOf c hU) =
      classOf (restrictedCocycle f hf c) (restrictedCover_covers f hU) := by
  have hmap := @Ext.mapExactFunctor_extClass
    (AbelianSheaf X) _ _ (AbelianSheaf T) _ _
    (Embedding.restriction f hf) (Embedding.restriction_additive f hf)
    (Embedding.restriction_preservesFiniteLimits f hf)
    (Embedding.restriction_preservesFiniteColimits f hf)
    (abelianSheaf_hasExt X) (abelianSheaf_hasExt T)
    (complex c) (complex_shortExact c hU)
  have hclass := CechConnecting.classOf_eq_connecting
    ((complex c).map (Embedding.restriction f hf))
    (restrictedCocycle f hf c) (restrictedCover_covers f hU) (Embedding.integerUnit f hf)
    (restrictedLocalSection f hf c) (restrictedLocalSection_projection_unit f hf c)
    (restrictedLocalSection_difference f hf c)
    ((complex_shortExact c hU).map_of_exact (Embedding.restriction f hf))
  exact (congrArg (fun a => (Ext.mk₀ (Embedding.integerUnit f hf)).comp a (zero_add 1))
    hmap).trans hclass.symm

/-- Every actual coefficient morphism on the embedding domain carries this
native restricted class to the class of the actual mapped cocycle. -/
theorem map_cohomologyMap_classOf {G : TopCat.Sheaf AddCommGrpCat.{0} T}
    (g : (Embedding.restriction f hf).obj F ⟶ G) :
    CategoryTheory.Sheaf.H.map g 1 (Embedding.cohomologyMap f hf F 1 (classOf c hU)) =
      classOf (HolomorphicPicard.Cech.mapCocycle g (restrictedCocycle f hf c))
        (restrictedCover_covers f hU) :=
  (congrArg (CategoryTheory.Sheaf.H.map g 1) (cohomologyMap_classOf f hf c hU)).trans
    (HolomorphicPicard.CechExtension.classOf_naturality g
      (restrictedCocycle f hf c) (restrictedCover_covers f hU))

end OpenClassRestriction.EmbeddingCech
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
