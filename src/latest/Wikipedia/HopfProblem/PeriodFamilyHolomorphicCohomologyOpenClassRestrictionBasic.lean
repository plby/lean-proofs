import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestriction

/-!
# Literal restriction of original Čech cocycles to an open subspace

The actual original coefficient sheaf maps to the pushforward of its
actual exact open restriction by literal section restriction. Applying
this map to the original cocycle gives the literal inverse-image cover
and its native restricted cocycle. This uses no finite-closed-map
cohomology comparison and no separation hypothesis.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicFunctionSheaf.SphereH1
open HolomorphicSheafCohomology

variable {X : TopCat.{0}} (A : Opens X)

/-- The original inclusion maps the inverse image of an ambient open
back into that same original ambient open. -/
theorem imagePreimage_le (V : Opens X) :
    (OpenRestriction.openImage A).obj (OpenRestriction.preimageOpen A V) ≤ V := by
  rintro x ⟨y, hy, rfl⟩
  exact hy

/-- Actual section restriction gives the genuine coefficient morphism
into the pushforward of the actual open-restricted sheaf. -/
def coefficientUnit (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat (OpenRestriction.inclusion A)).obj
      ((OpenRestriction.restriction A).obj F) where
  hom :=
    { app V := F.obj.map (homOfLE (imagePreimage_le A V.unop)).op
      naturality V W h := by
        let v := (homOfLE (imagePreimage_le A V.unop)).op
        let w := (homOfLE (imagePreimage_le A W.unop)).op
        let r := ((OpenRestriction.openImage A).map
          ((Opens.map (OpenRestriction.inclusion A)).map h.unop)).op
        change F.obj.map h ≫ F.obj.map w = F.obj.map v ≫ F.obj.map r
        exact (F.obj.map_comp h w).symm.trans
          ((congrArg F.obj.map (Subsingleton.elim (h ≫ w) (v ≫ r))).trans
            (F.obj.map_comp v r)) }

/-- The coefficient map is literally the original section restriction. -/
@[simp] theorem coefficientUnit_app (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (V : Opens X) (s : Section F V) :
    (coefficientUnit A F).hom.app (op V) s = res F (imagePreimage_le A V) s := rfl

/-- The genuine coefficient morphism is natural in the original sheaf. -/
@[reassoc] theorem coefficientUnit_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (g : F ⟶ G) :
    coefficientUnit A F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (OpenRestriction.inclusion A)).map
          ((OpenRestriction.restriction A).map g) = g ≫ coefficientUnit A G := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  exact g.hom.naturality (homOfLE (imagePreimage_le A V.unop)).op

/-- Restrictions of the actual restricted sheaf are literally the
original sheaf restrictions along the actual image-open maps. -/
theorem restricted_res (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {V W : Opens A} (h : V ≤ W) (s : Section ((OpenRestriction.restriction A).obj F) W) :
    res ((OpenRestriction.restriction A).obj F) h s =
      res F ((OpenRestriction.openImage A).map (homOfLE h)).le s := rfl

/-- The cover consists of the literal inverse images of the original opens. -/
abbrev restrictedCover {ι : Type} (U : ι → Opens X) : ι → Opens A :=
  fun i => OpenRestriction.preimageOpen A (U i)

/-- The proved original cover covers the entire original open subspace. -/
theorem restrictedCover_covers {ι : Type} {U : ι → Opens X}
    (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    ∀ x : A, ∃ i : ι, x ∈ restrictedCover A U i := fun x => hU x

/-- The actual cocycle of the actual restricted coefficient sheaf,
defined by literal section restriction on the original inverse-image cover. -/
def restrictedCocycle {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U) :
    CechOneCocycle ((OpenRestriction.restriction A).obj F) (restrictedCover A U) :=
  CechFibre.pullbackCocycle (OpenRestriction.inclusion A) (coefficientUnit A F) c

/-- Each native restricted cocycle value is the stated literal restriction. -/
@[simp] theorem restrictedCocycle_value {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U) (i j : ι) :
    (restrictedCocycle A c).value i j =
      res F (imagePreimage_le A (U i ⊓ U j)) (c.value i j) := rfl

/-- Restricting actual cocycle coefficients commutes with the original
restricted coefficient sheaf morphism. -/
theorem restrictedCocycle_map {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (g : F ⟶ G) {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U) :
    restrictedCocycle A (HolomorphicPicard.Cech.mapCocycle g c) =
      HolomorphicPicard.Cech.mapCocycle ((OpenRestriction.restriction A).map g)
        (restrictedCocycle A c) := by
  apply HolomorphicPicard.Cech.cocycle_ext
  intro i j
  exact res_map g (imagePreimage_le A (U i ⊓ U j)) (c.value i j)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
