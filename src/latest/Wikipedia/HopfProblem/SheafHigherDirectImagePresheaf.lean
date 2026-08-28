import Wikipedia.HopfProblem.SheafHigherDirectImageResolution

/-!
# Presheaf pushforward and resolution cohomology

Unlike sheaf pushforward, presheaf pushforward is exact: it is literal
precomposition with the inverse-image functor on open sets.  This
identifies the cohomology presheaf of a pushed-forward resolution with
the pushed-forward cohomology presheaf of the source resolution.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The actual presheaf pushforward, given by inverse-image evaluation. -/
abbrev presheafPushforward : TopCat.Presheaf AddCommGrpCat.{0} X ⥤
    TopCat.Presheaf AddCommGrpCat.{0} Y :=
  TopCat.Presheaf.pushforward AddCommGrpCat f

instance presheafPushforward_additive : (presheafPushforward f).Additive where
  map_add := by intros; rfl

instance presheafPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (presheafPushforward f) :=
  inferInstanceAs (PreservesFiniteLimits
    ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (Opens.map f).op))

instance presheafPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (presheafPushforward f) :=
  inferInstanceAs (PreservesFiniteColimits
    ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (Opens.map f).op))

/-- Presheaf pushforward commutes with the actual homology presheaf
of every sheaf complex. -/
def homologyPresheafPushforwardIso (K : CochainComplex (AbelianSheaf X) ℕ) (n : ℕ) :
    homologyPresheaf (((pushforward f).mapHomologicalComplex _).obj K) n ≅
      (Opens.map f).op ⋙ homologyPresheaf K n :=
  mapComplexHomologyIso (underlyingPresheafComplex K) (presheafPushforward f) n

/-- In particular, the local cohomology of a pushed-forward injective
resolution is evaluated on the actual source inverse-image opens. -/
def resolutionPresheafPushforwardIso {F : AbelianSheaf X}
    (I : InjectiveResolution F) (n : ℕ) :
    resolutionPresheaf f I n ≅ (Opens.map f).op ⋙ homologyPresheaf I.cocomplex n :=
  homologyPresheafPushforwardIso f I.cocomplex n

end Wikipedia.HopfProblem.SheafHigherDirectImage
