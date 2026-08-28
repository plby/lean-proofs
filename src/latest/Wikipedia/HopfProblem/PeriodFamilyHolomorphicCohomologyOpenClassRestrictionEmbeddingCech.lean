import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCechClass

/-!
# Native open-embedding Čech transport with arbitrary coefficient maps

Restriction followed by any actual coefficient sheaf morphism is represented
by the literal inverse-image cocycle under the composed original coefficient
map into pushforward. Both the original Ext restriction and the original
Čech extension classes are unchanged constructions.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.EmbeddingCech

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension

variable {T X : TopCat.{0}} (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)
  {F : TopCat.Sheaf AddCommGrpCat.{0} X} {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U)

/-- Mapping the genuine restricted cocycle is the actual inverse-image
cocycle for the literal composed coefficient map into pushforward. -/
theorem map_restrictedCocycle {G : TopCat.Sheaf AddCommGrpCat.{0} T}
    (g : (Embedding.restriction f hf).obj F ⟶ G) :
    HolomorphicPicard.Cech.mapCocycle g (restrictedCocycle f hf c) =
      CechFibre.pullbackCocycle f
        (coefficientUnit f hf F ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map g) c := by
  apply HolomorphicPicard.Cech.cocycle_ext
  intro i j
  rfl

/-- Actual native cohomology restriction followed by any actual coefficient
morphism has precisely the genuine Čech class of the literal pullback cocycle.
Only the given open embedding and original covering are required. -/
theorem map_cohomologyMap_classOf_pullback (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
    {G : TopCat.Sheaf AddCommGrpCat.{0} T}
    (g : (Embedding.restriction f hf).obj F ⟶ G) :
    CategoryTheory.Sheaf.H.map g 1 (Embedding.cohomologyMap f hf F 1 (classOf c hU)) =
      classOf (CechFibre.pullbackCocycle f
        (coefficientUnit f hf F ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map g) c)
          (CechFibre.pullbackCover_covers f hU) :=
  (map_cohomologyMap_classOf f hf c hU g).trans
    (congrArg (fun d : CechOneCocycle G (restrictedCover f U) =>
      classOf d (restrictedCover_covers f hU)) (map_restrictedCocycle f hf c g))

end OpenClassRestriction.EmbeddingCech
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
