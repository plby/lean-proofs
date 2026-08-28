import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingExact

/-!
# Literal Čech restriction along an actual open embedding

The coefficient map is genuine restriction to the image of an inverse-image
open. The cover is the original inverse-image cover, and the cocycle uses the
original section maps into the actual restricted coefficient sheaf.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.EmbeddingCech

open HolomorphicFunctionSheaf.SphereH1

variable {T X : TopCat.{0}} (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)

/-- Literal section restriction gives the actual coefficient morphism into
the pushforward of the original open-embedding restriction. -/
def coefficientUnit (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj
      ((Embedding.restriction f hf).obj F) where
  hom :=
    { app V := F.obj.map (homOfLE (Embedding.imagePreimage_le f hf V.unop)).op
      naturality V W h := by
        let v := (homOfLE (Embedding.imagePreimage_le f hf V.unop)).op
        let w := (homOfLE (Embedding.imagePreimage_le f hf W.unop)).op
        let r := ((Embedding.openImage f hf).map ((Opens.map f).map h.unop)).op
        change F.obj.map h ≫ F.obj.map w = F.obj.map v ≫ F.obj.map r
        exact (F.obj.map_comp h w).symm.trans
          ((congrArg F.obj.map (Subsingleton.elim (h ≫ w) (v ≫ r))).trans
            (F.obj.map_comp v r)) }

/-- The coefficient map evaluates by the actual ambient restriction map. -/
@[simp] theorem coefficientUnit_app (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (V : Opens X) (s : Section F V) :
    (coefficientUnit f hf F).hom.app (op V) s =
      res F (Embedding.imagePreimage_le f hf V) s := rfl

/-- The original coefficient map is natural in actual sheaf morphisms. -/
@[reassoc] theorem coefficientUnit_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (g : F ⟶ G) :
    coefficientUnit f hf F ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map
        ((Embedding.restriction f hf).map g) = g ≫ coefficientUnit f hf G := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  exact g.hom.naturality (homOfLE (Embedding.imagePreimage_le f hf V.unop)).op

/-- The cover consists of literal inverse images of the original covering opens. -/
abbrev restrictedCover {ι : Type} (U : ι → Opens X) : ι → Opens T :=
  fun i => Embedding.preimageOpen f (U i)

/-- An original covering pulls back to a covering of the actual embedding domain. -/
theorem restrictedCover_covers {ι : Type} {U : ι → Opens X}
    (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    ∀ t : T, ∃ i : ι, t ∈ restrictedCover f U i := fun t => hU (f t)

/-- The genuine restricted cocycle is the original inverse-image cocycle under
the literal section-restriction coefficient morphism. -/
def restrictedCocycle {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U) :
    CechOneCocycle ((Embedding.restriction f hf).obj F) (restrictedCover f U) :=
  CechFibre.pullbackCocycle f (coefficientUnit f hf F) c

/-- Every original cocycle value is restricted to the literal image of its inverse image. -/
@[simp] theorem restrictedCocycle_value {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U) (i j : ι) :
    (restrictedCocycle f hf c).value i j =
      res F (Embedding.imagePreimage_le f hf (U i ⊓ U j)) (c.value i j) := rfl

/-- Original coefficient maps commute with actual restriction of the cocycle. -/
theorem restrictedCocycle_map {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (g : F ⟶ G) {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U) :
    restrictedCocycle f hf (HolomorphicPicard.Cech.mapCocycle g c) =
      HolomorphicPicard.Cech.mapCocycle ((Embedding.restriction f hf).map g)
        (restrictedCocycle f hf c) := by
  apply HolomorphicPicard.Cech.cocycle_ext
  intro i j
  exact res_map g (Embedding.imagePreimage_le f hf (U i ⊓ U j)) (c.value i j)

end OpenClassRestriction.EmbeddingCech
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
