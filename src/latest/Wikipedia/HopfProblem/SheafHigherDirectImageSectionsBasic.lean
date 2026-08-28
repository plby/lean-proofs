import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestrictionGlobal
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Free open sheaves and the actual section presheaf

The free abelian sheaf on the Yoneda presheaf of an open set represents
sections on that open set.  The comparison below is natural both in the
sheaf and in the open, using the actual sheafification and restriction
maps.  In particular it identifies presheaves, not just their objects.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafHigherDirectImage.Sections

open HolomorphicSheafCohomology.OpenRestriction

variable {X : TopCat.{0}}

/-- The actual free-open-sheaf functor appearing in Mathlib's
cohomology presheaf. -/
abbrev freeOpenFunctor (X : TopCat.{0}) : Opens X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat

/-- Representing sections commute with the genuine restriction map
for an inclusion of open sets. -/
theorem freeHomEquiv_naturality_open {U V : Opens X} (i : U ⟶ V)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (h : freeOpen V ⟶ F) :
    freeHomEquiv U F ((freeOpenFunctor X).map i ≫ h) =
      F.obj.map i.op (freeHomEquiv V F h) := by
  let e₁ := sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat
  let e₂ := Adjunction.whiskerRight (Opens X)ᵒᵖ AddCommGrpCat.adj
  have h₁ := e₁.homEquiv_naturality_left
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map i)) h
  have h₂ := e₂.homEquiv_naturality_left (yoneda.map i) (e₁.homEquiv _ F h)
  change yonedaEquiv (e₂.homEquiv _ F.obj
      (e₁.homEquiv _ F ((freeOpenFunctor X).map i ≫ h))) =
    (F.obj ⋙ forget AddCommGrpCat).map i.op
      (yonedaEquiv (e₂.homEquiv _ F.obj (e₁.homEquiv _ F h)))
  exact (congrArg (fun a => yonedaEquiv (e₂.homEquiv _ F.obj a)) h₁).trans
    ((congrArg yonedaEquiv h₂).trans (yonedaEquiv_naturality _ i).symm)

/-- Additive form of the same open-set naturality statement. -/
theorem freeHomAddEquiv_naturality_open {U V : Opens X} (i : U ⟶ V)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (h : freeOpen V ⟶ F) :
    freeHomAddEquiv U F ((freeOpenFunctor X).map i ≫ h) =
      F.obj.map i.op (freeHomAddEquiv V F h) :=
  freeHomEquiv_naturality_open i F h

/-- The usual sections-on-an-open functor on the category of sheaves. -/
abbrev sectionsFunctor (U : Opens X) : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  (TopCat.Sheaf.forget AddCommGrpCat X).flip.obj (op U)

/-- Sections on an open are represented by its actual free sheaf,
naturally in the coefficient sheaf. -/
def freeOpenSectionsIso (U : Opens X) :
    preadditiveCoyoneda.obj (op (freeOpen U)) ≅ sectionsFunctor U :=
  NatIso.ofComponents
    (fun F => (freeHomAddEquiv U F).toAddCommGrpIso)
    (fun f => by
      ext h
      exact freeHomEquiv_naturality U h f)

/-- The representing-section comparison is natural in both variables. -/
def freeOpenCoyonedaIso (X : TopCat.{0}) :
    (freeOpenFunctor X).op ⋙ preadditiveCoyoneda ≅
      (TopCat.Sheaf.forget AddCommGrpCat X).flip :=
  NatIso.ofComponents
    (fun U => freeOpenSectionsIso U.unop)
    (fun i => by
      ext F h
      exact freeHomEquiv_naturality_open i.unop F h)

/-- The induced isomorphism is the genuine section presheaf of the
given sheaf. -/
def freeOpenHomPresheafIso (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    ((freeOpenFunctor X).op ⋙ preadditiveCoyoneda).flip.obj F ≅ F.obj :=
  NatIso.ofComponents
    (fun U => (freeHomAddEquiv U.unop F).toAddCommGrpIso)
    (fun i => by
      ext h
      exact freeHomEquiv_naturality_open i.unop F h)

end Wikipedia.HopfProblem.SheafHigherDirectImage.Sections
