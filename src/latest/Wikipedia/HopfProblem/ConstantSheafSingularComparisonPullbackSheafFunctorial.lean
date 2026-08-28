import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafRawNaturality
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafBasic

/-!
# Functoriality of the actual cochain and constant sheaf pullbacks

The native sheafification unit determines maps into each actual
pushforward sheaf. Thus the original raw identity and composition laws
give identity and composition for the genuine cochain sheaf maps and
constant sheaf maps. No surjectivity on sections of the unit is used.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf

open Sheafification

variable {X Y Z : TopCat.{0}}

/-- The actual extension of the identity raw map is the identity sheaf
map, using the native identity-pushforward identification. -/
theorem sheafifyPullback_id (P : TopCat.Presheaf AddCommGrpCat.{0} X) :
    sheafifyPullback (𝟙 X) (𝟙 P) = 𝟙 (sheaf P) := by
  apply lift_hom_ext (𝟙 X)
  change unit P ≫ (sheafifyPullback (𝟙 X) (𝟙 P)).hom = unit P ≫ 𝟙 _
  have h : unit P ≫ (sheafifyPullback (𝟙 X) (𝟙 P)).hom = 𝟙 P ≫ unit P :=
    unit_sheafifyPullback (𝟙 X) (𝟙 P)
  exact h.trans ((Category.id_comp (unit P)).trans (Category.comp_id (unit P)).symm)

/-- Extending a composite raw map agrees with composing the actual
sheaf extensions and the genuine pushforward of the second extension. -/
theorem sheafifyPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : TopCat.Presheaf AddCommGrpCat.{0} Z}
    {Q : TopCat.Presheaf AddCommGrpCat.{0} Y}
    {R : TopCat.Presheaf AddCommGrpCat.{0} X}
    (η : P ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat g).obj Q)
    (θ : Q ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat f).obj R) :
    sheafifyPullback (f ≫ g)
        (η ≫ (TopCat.Presheaf.pushforward AddCommGrpCat g).map θ) =
      sheafifyPullback g η ≫ (TopCat.Sheaf.pushforward AddCommGrpCat g).map
        (sheafifyPullback f θ) := by
  apply lift_hom_ext (f ≫ g)
  let F := TopCat.Presheaf.pushforward AddCommGrpCat f
  let G := TopCat.Presheaf.pushforward AddCommGrpCat g
  let a : (sheaf P).obj ⟶ G.obj (sheaf Q).obj := (sheafifyPullback g η).hom
  let b : (sheaf Q).obj ⟶ F.obj (sheaf R).obj := (sheafifyPullback f θ).hom
  have ha : unit P ≫ a = η ≫ G.map (unit Q) := unit_sheafifyPullback g η
  have hb : unit Q ≫ b = θ ≫ F.map (unit R) := unit_sheafifyPullback f θ
  have h₁ : unit P ≫ (a ≫ G.map b) = η ≫ (G.map (unit Q) ≫ G.map b) :=
    (Category.assoc (unit P) a (G.map b)).symm.trans
      ((congrArg (fun k => k ≫ G.map b) ha).trans
        (Category.assoc η (G.map (unit Q)) (G.map b)))
  have h₂ : η ≫ (G.map (unit Q) ≫ G.map b) = η ≫ G.map (unit Q ≫ b) :=
    congrArg (fun k => η ≫ k) (G.map_comp (unit Q) b).symm
  have h₃ : η ≫ G.map (unit Q ≫ b) = η ≫ G.map (θ ≫ F.map (unit R)) :=
    congrArg (fun k => η ≫ G.map k) hb
  have h₄ : η ≫ G.map (θ ≫ F.map (unit R)) =
      (η ≫ G.map θ) ≫ G.map (F.map (unit R)) :=
    (congrArg (fun k => η ≫ k) (G.map_comp θ (F.map (unit R)))).trans
      (Category.assoc η (G.map θ) (G.map (F.map (unit R)))).symm
  change unit P ≫ (sheafifyPullback (f ≫ g) (η ≫ G.map θ)).hom =
    unit P ≫ (a ≫ G.map b)
  exact (unit_sheafifyPullback (f ≫ g) (η ≫ G.map θ)).trans
    (h₁.trans (h₂.trans (h₃.trans h₄))).symm

variable (A : AddCommGrpCat.{0}) (n : ℕ)

/-- The actual cochain sheaf pullback along the identity is the identity. -/
@[simp] theorem cochainPullback_id :
    cochainPullback (𝟙 X) A n = 𝟙 (cochainSheaf X A n) := by
  change sheafifyPullback (𝟙 X) (rawPullback (𝟙 X) A n) = _
  rw [rawPullback_id]
  exact sheafifyPullback_id (cochainPresheaf X A n)

/-- Actual cochain sheaf pullbacks compose contravariantly into the
original composite-pushforward object. -/
theorem cochainPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    cochainPullback (f ≫ g) A n =
      cochainPullback g A n ≫ (TopCat.Sheaf.pushforward AddCommGrpCat g).map
        (cochainPullback f A n) := by
  change sheafifyPullback (f ≫ g) (rawPullback (f ≫ g) A n) = _
  rw [rawPullback_comp]
  exact sheafifyPullback_comp f g (rawPullback g A n) (rawPullback f A n)

/-- The literal constant-presheaf identity law. -/
@[simp] theorem rawConstantPullback_id :
    rawConstantPullback (𝟙 X) A =
      𝟙 (ConstantSheafFirstCohomology.Constant.presheaf X A) := by
  apply NatTrans.ext
  funext U
  rfl

/-- Literal coefficient values are unchanged under a composite raw
constant-presheaf pullback. -/
theorem rawConstantPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    rawConstantPullback (f ≫ g) A =
      rawConstantPullback g A ≫ (TopCat.Presheaf.pushforward AddCommGrpCat g).map
        (rawConstantPullback f A) := by
  apply NatTrans.ext
  funext U
  change 𝟙 A = 𝟙 A ≫ 𝟙 A
  exact (Category.id_comp (𝟙 A)).symm

/-- The actual constant sheaf pullback along the identity is the identity. -/
@[simp] theorem constantPullback_id :
    constantPullback (𝟙 X) A =
      𝟙 (ConstantSheafFirstCohomology.Constant.sheaf X A) := by
  change sheafifyPullback (𝟙 X) (rawConstantPullback (𝟙 X) A) = _
  rw [rawConstantPullback_id]
  exact sheafifyPullback_id (ConstantSheafFirstCohomology.Constant.presheaf X A)

/-- Actual constant sheaf pullbacks compose through the native
pushforward functor. -/
theorem constantPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    constantPullback (f ≫ g) A =
      constantPullback g A ≫ (TopCat.Sheaf.pushforward AddCommGrpCat g).map
        (constantPullback f A) := by
  change sheafifyPullback (f ≫ g) (rawConstantPullback (f ≫ g) A) = _
  rw [rawConstantPullback_comp]
  exact sheafifyPullback_comp f g (rawConstantPullback g A) (rawConstantPullback f A)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf
