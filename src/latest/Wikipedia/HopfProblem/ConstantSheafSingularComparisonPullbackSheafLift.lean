import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSheafifyBasic
import Mathlib.Topology.Sheaves.Functors

/-!
# Actual sheafification maps into native pushforward sheaves

A map from a presheaf to the underlying presheaf of an actual pushforward
sheaf extends uniquely through the native sheafification unit. In
particular, a raw map between presheaves on two spaces gives a map from
the sheafification on the target into the genuine pushforward of the
sheafification on the source. Naturality follows from the original units.

Only the sheaf property of the actual pushforward is used; no exactness
of pushforward is imposed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf

open Sheafification

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- Extend an original presheaf map through the native sheafification
unit to the original pushforward sheaf. -/
def liftToPushforward {P : TopCat.Presheaf AddCommGrpCat.{0} Y}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (η : P ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).obj) :
    sheaf P ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj F :=
  ⟨CategoryTheory.sheafifyLift (Opens.grothendieckTopology Y) η
    ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).property⟩

/-- The lift retains the original map on every original unit representative. -/
@[reassoc]
theorem unit_liftToPushforward {P : TopCat.Presheaf AddCommGrpCat.{0} Y}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (η : P ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).obj) :
    unit P ≫ (liftToPushforward f F η).hom = η :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology Y) η
    ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).property

/-- Original unit representatives determine a sheaf map into the actual
pushforward, even though the unit need not be surjective on sections. -/
theorem lift_hom_ext {P : TopCat.Presheaf AddCommGrpCat.{0} Y}
    {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {a b : sheaf P ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj F}
    (h : unit P ≫ a.hom = unit P ≫ b.hom) : a = b := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology Y) a.hom b.hom
    ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).property h

/-- A raw presheaf pullback induces a map between the native
sheafifications, with the original pushforward as target. -/
def sheafifyPullback {P : TopCat.Presheaf AddCommGrpCat.{0} Y}
    {Q : TopCat.Presheaf AddCommGrpCat.{0} X}
    (η : P ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat f).obj Q) :
    sheaf P ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj (sheaf Q) :=
  liftToPushforward f (sheaf Q)
    (η ≫ (TopCat.Presheaf.pushforward AddCommGrpCat f).map (unit Q))

/-- The induced map is exactly the raw map followed by the original
unit on the preimage open. -/
@[reassoc]
theorem unit_sheafifyPullback {P : TopCat.Presheaf AddCommGrpCat.{0} Y}
    {Q : TopCat.Presheaf AddCommGrpCat.{0} X}
    (η : P ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat f).obj Q) :
    unit P ≫ (sheafifyPullback f η).hom =
      η ≫ (TopCat.Presheaf.pushforward AddCommGrpCat f).map (unit Q) :=
  unit_liftToPushforward f (sheaf Q) _

/-- A commuting square of the original presheaf maps gives a commuting
square of their actual sheafifications and actual pushforwards. -/
theorem sheafifyPullback_naturality
    {P₁ P₂ : TopCat.Presheaf AddCommGrpCat.{0} Y}
    {Q₁ Q₂ : TopCat.Presheaf AddCommGrpCat.{0} X}
    (α : P₁ ⟶ P₂) (β : Q₁ ⟶ Q₂)
    (η₁ : P₁ ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat f).obj Q₁)
    (η₂ : P₂ ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat f).obj Q₂)
    (h : α ≫ η₂ = η₁ ≫ (TopCat.Presheaf.pushforward AddCommGrpCat f).map β) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map α ≫
        sheafifyPullback f η₂ =
      sheafifyPullback f η₁ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map β) := by
  apply lift_hom_ext f
  let R := TopCat.Presheaf.pushforward AddCommGrpCat f
  let α' := (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map α
  let β' := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map β
  have hα : unit P₁ ≫ α'.hom = α ≫ unit P₂ :=
    (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology Y) α).symm
  have hβ : β ≫ unit Q₂ = unit Q₁ ≫ β'.hom :=
    CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X) β
  have hu₁ : unit P₁ ≫ (sheafifyPullback f η₁).hom = η₁ ≫ R.map (unit Q₁) :=
    unit_sheafifyPullback f η₁
  change unit P₁ ≫ (α'.hom ≫ (sheafifyPullback f η₂).hom) =
    unit P₁ ≫ ((sheafifyPullback f η₁).hom ≫ R.map β'.hom)
  have h₁ : unit P₁ ≫ (α'.hom ≫ (sheafifyPullback f η₂).hom) =
      α ≫ (η₂ ≫ R.map (unit Q₂)) := by
    rw [← Category.assoc, hα, Category.assoc, unit_sheafifyPullback]
    rfl
  have h₂ : α ≫ (η₂ ≫ R.map (unit Q₂)) =
      η₁ ≫ (R.map β ≫ R.map (unit Q₂)) := by
    rw [← Category.assoc, h, Category.assoc]
  have h₃ : η₁ ≫ (R.map β ≫ R.map (unit Q₂)) =
      η₁ ≫ R.map (unit Q₁ ≫ β'.hom) := by
    rw [← R.map_comp, hβ]
  have h₄ : η₁ ≫ R.map (unit Q₁ ≫ β'.hom) =
      η₁ ≫ (R.map (unit Q₁) ≫ R.map β'.hom) := by
    rw [R.map_comp]
  have h₅ : η₁ ≫ (R.map (unit Q₁) ≫ R.map β'.hom) =
      unit P₁ ≫ ((sheafifyPullback f η₁).hom ≫ R.map β'.hom) := by
    rw [← Category.assoc, ← hu₁]
    exact Category.assoc (unit P₁) (sheafifyPullback f η₁).hom (R.map β'.hom)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf
