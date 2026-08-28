import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbedding
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionImageInteger

/-!
# Genuine integer endpoints under composition of open embeddings

Each endpoint is the original constant-presheaf sheafification map.
The actual composition and identity isomorphisms of restriction sheaves
preserve the original constant integer sections, hence identify these
endpoints without any endpoint-isomorphism premise.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.Embedding

open CuspNormalization.SheafCohomologyFinitePushforward
open HolomorphicPicard.CechExtension

variable {T X : TopCat.{0}} (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)

/-- The actual constant-presheaf endpoint for the genuine restriction functor. -/
abbrev integerUnit : integerSheaf T ⟶ (restriction f hf).obj (integerSheaf X) :=
  ImageInteger.unit (T := T) (X := X) (openImage f hf)

/-- The native endpoint retains every original integer section on every image open. -/
theorem integerUnit_degreeUnit_app (W : Opens T) (n : ULift.{0} ℤ) :
    (integerUnit f hf).hom.app (op W) ((degreeUnit T).app (op W) n) =
      (degreeUnit X).app (op ((openImage f hf).obj W)) n :=
  ImageInteger.unit_degreeUnit_app (T := T) (X := X) (openImage f hf) W n

/-- The composition isomorphism gives exactly the actual composite integer endpoint. -/
theorem integerUnit_comp {S : TopCat.{0}} (g : S ⟶ T) (hg : Topology.IsOpenEmbedding g) :
    integerUnit g hg ≫ (restriction g hg).map (integerUnit f hf) ≫
        (restrictionCompIso f hf g hg).hom.app (integerSheaf X) =
      integerUnit (g ≫ f) (hf.comp hg) := by
  apply ImageInteger.unit_unique (T := S) (X := X) (openImage (g ≫ f) (hf.comp hg))
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro n
  change (((restrictionCompIso f hf g hg).hom.app (integerSheaf X)).hom.app (op W.unop))
      ((integerUnit f hf).hom.app (op ((openImage g hg).obj W.unop))
        ((integerUnit g hg).hom.app (op W.unop) ((degreeUnit S).app (op W.unop) n))) =
    (degreeUnit X).app (op ((openImage (g ≫ f) (hf.comp hg)).obj W.unop)) n
  let r := (eqToHom (openImage_comp_obj f hf g hg W.unop).symm).op
  have hd := (congrArg
    ((integerUnit f hf).hom.app (op ((openImage g hg).obj W.unop)))
    (integerUnit_degreeUnit_app g hg W.unop n)).trans
      (integerUnit_degreeUnit_app f hf ((openImage g hg).obj W.unop) n)
  exact (ConcreteCategory.congr_hom
    (restrictionCompIso_hom_app f hf g hg (integerSheaf X) W.unop) _).trans
    ((congrArg ((integerSheaf X).obj.map r) hd).trans
      (ConcreteCategory.congr_hom ((degreeUnit X).naturality r) n).symm)

/-- The identity comparison carries the actual endpoint to the original identity map. -/
theorem integerUnit_id (X : TopCat.{0}) :
    integerUnit (𝟙 X) Topology.IsOpenEmbedding.id ≫
        (restrictionIdIso X).hom.app (integerSheaf X) = 𝟙 (integerSheaf X) := by
  have h := ImageInteger.unit_unique (T := X) (X := X) (𝟭 (Opens X))
    (integerUnit (𝟙 X) Topology.IsOpenEmbedding.id ≫
      (restrictionIdIso X).hom.app (integerSheaf X))
  refine (h ?_).trans (ImageInteger.unit_id X)
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro n
  change (((restrictionIdIso X).hom.app (integerSheaf X)).hom.app (op W.unop))
      ((integerUnit (𝟙 X) Topology.IsOpenEmbedding.id).hom.app (op W.unop)
        ((degreeUnit X).app (op W.unop) n)) = (degreeUnit X).app (op W.unop) n
  let r := (eqToHom (openImage_id_obj X W.unop).symm).op
  exact (ConcreteCategory.congr_hom
    (restrictionIdIso_hom_app X (integerSheaf X) W.unop) _).trans
    ((congrArg ((integerSheaf X).obj.map r)
      (integerUnit_degreeUnit_app (𝟙 X) Topology.IsOpenEmbedding.id W.unop n)).trans
      (ConcreteCategory.congr_hom ((degreeUnit X).naturality r) n).symm)

end OpenClassRestriction.Embedding
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
