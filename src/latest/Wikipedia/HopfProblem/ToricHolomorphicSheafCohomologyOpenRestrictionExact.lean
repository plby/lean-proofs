import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestrictionLan
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Actual open restriction is exact and preserves injectives

The image functor of actual opens is both continuous and cocontinuous:
every covering of an open in the subspace lifts by actual preimages.
Its sheaf restriction consequently has both adjoints. Its left adjoint
is actual abelian extension by zero, whose preservation of
monomorphisms follows from the pointwise Kan-extension calculation.
This proves exactness and preservation of injectives, without assuming
an open-subspace cohomology comparison.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenRestriction

variable {X : TopCat.{0}} (U : Opens X)

instance openImage_continuous :
    (openImage U).IsContinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) :=
  (inclusion_isOpenEmbedding U).functor_isContinuous

/-- Actual coverings lift along the open inclusion. -/
instance openImage_cocontinuous :
    (openImage U).IsCocontinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) where
  cover_lift {V S} hS := by
    intro x hx
    obtain ⟨W, i, hi, hxW⟩ := hS x.val ⟨x, hx, rfl⟩
    let W' := preimageOpen U W
    have hW'V : W' ≤ V := by
      intro y hy
      obtain ⟨z, hz, he⟩ := i.le hy
      have hzy : z = y := Subtype.ext he
      exact hzy ▸ hz
    let k : (openImage U).obj W' ⟶ W := homOfLE (by
      rintro y ⟨z, hz, rfl⟩
      exact hz)
    refine ⟨W', homOfLE hW'V, ?_, hxW⟩
    exact S.downward_closed hi k

/-- The genuine restriction functor on actual abelian sheaves. -/
abbrev restriction : TopCat.Sheaf AddCommGrpCat.{0} X ⥤
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of U) :=
  (openImage U).sheafPushforwardContinuous AddCommGrpCat
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)

theorem restriction_eq_sheafRestrict : restriction U = U.sheafRestrict := rfl

instance restriction_additive : (restriction U).Additive where
  map_add := by intros; rfl

instance restriction_rightAdjoint : (restriction U).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (openImage U)
    AddCommGrpCat (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).isRightAdjoint

instance restriction_leftAdjoint : (restriction U).IsLeftAdjoint :=
  ((openImage U).sheafAdjunctionCocontinuous AddCommGrpCat
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).isLeftAdjoint

instance restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction U) := by
  infer_instance

instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction U) := by
  infer_instance

/-- The actual sheafification of presheaf extension by zero. -/
abbrev extension : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of U) ⥤
    TopCat.Sheaf AddCommGrpCat.{0} X :=
  Functor.sheafPullbackConstruction.sheafPullback (openImage U) AddCommGrpCat
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)

/-- Sheafification and the proved actual Kan extension both preserve monos. -/
instance extension_preservesMonomorphisms : (extension U).PreservesMonomorphisms := by
  change (sheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat ⋙
    (openImage U).op.lan ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).PreservesMonomorphisms
  infer_instance

/-- Actual open restriction preserves injective abelian sheaves. -/
instance restriction_preservesInjectiveObjects : (restriction U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (openImage U)
      AddCommGrpCat (Opens.grothendieckTopology U) (Opens.grothendieckTopology X))

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenRestriction
