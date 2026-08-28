import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Actual skyscraper targets for stalk evaluation

These are the existing skyscraper sheaf and its actual stalk adjunction.
The formulas below identify the components on neighborhoods of the
support point and the induced map on its categorical stalk. No
decidability assumptions occur in the public interfaces.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation

attribute [local instance] Classical.propDecidable

variable {X : TopCat.{0}}

/-- Mathlib's actual additive skyscraper sheaf with value `A` at `b`. -/
abbrev skyscraper (b : X) (A : AddCommGrpCat.{0}) :
    TopCat.Sheaf AddCommGrpCat.{0} X :=
  skyscraperSheaf b A

/-- On an actual neighborhood of its support, the skyscraper's section
group is canonically its coefficient group. -/
def skyscraperSectionIso (b : X) (A : AddCommGrpCat.{0})
    (U : Opens X) (hb : b ∈ U) :
    (skyscraper b A).presheaf.obj (op U) ≅ A :=
  eqToIso (if_pos hb)

/-- On an open set missing the support, the actual section group is a
terminal object. -/
def skyscraperSectionIsTerminal (b : X) (A : AddCommGrpCat.{0})
    (U : Opens X) (hb : b ∉ U) :
    IsTerminal ((skyscraper b A).presheaf.obj (op U)) :=
  isTerminalSkyscraperSheafObjObjOfNotMem hb

/-- The actual categorical stalk of the skyscraper at its support is
canonically its coefficient group. -/
def skyscraperStalkIso (b : X) (A : AddCommGrpCat.{0}) :
    (skyscraper b A).presheaf.stalk b ≅ A :=
  skyscraperPresheafStalkOfSpecializes b A specializes_rfl

/-- The actual section-germ map agrees with the neighborhood section
identification after passing to the canonical skyscraper stalk. -/
@[reassoc (attr := simp)] theorem germ_skyscraperStalkIso_hom
    (b : X) (A : AddCommGrpCat.{0}) (U : Opens X) (hb : b ∈ U) :
    (skyscraper b A).presheaf.germ U b hb ≫ (skyscraperStalkIso b A).hom =
      (skyscraperSectionIso b A U hb).hom :=
  germ_skyscraperPresheafStalkOfSpecializes_hom b A specializes_rfl U hb

/-- A homomorphism out of the actual stalk defines an actual sheaf
morphism to the skyscraper through Mathlib's stalk adjunction. -/
def toSkyscraper (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (b : X) (A : AddCommGrpCat.{0}) (φ : F.presheaf.stalk b ⟶ A) :
    F ⟶ skyscraper b A :=
  ⟨StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf b φ⟩

/-- On a neighborhood of the support, the sheaf morphism is precisely
the section-germ map followed by the given stalk homomorphism. -/
@[reassoc] theorem toSkyscraper_app
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (b : X) (A : AddCommGrpCat.{0}) (φ : F.presheaf.stalk b ⟶ A)
    (U : Opens X) (hb : b ∈ U) :
    (toSkyscraper F b A φ).hom.app (op U) ≫
        (skyscraperSectionIso b A U hb).hom = F.presheaf.germ U b hb ≫ φ := by
  exact (StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk b
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf b φ) U hb).symm.trans
      (congrArg (fun k => F.presheaf.germ U b hb ≫ k)
        (StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper b φ))

/-- The induced actual stalk map is the original homomorphism after
the canonical skyscraper-stalk identification. -/
@[reassoc] theorem toSkyscraper_stalk
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (b : X) (A : AddCommGrpCat.{0}) (φ : F.presheaf.stalk b ⟶ A) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map (toSkyscraper F b A φ).hom ≫
        (skyscraperStalkIso b A).hom = φ := by
  apply F.presheaf.stalk_hom_ext
  intro U hb
  calc
    F.presheaf.germ U b hb ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map (toSkyscraper F b A φ).hom ≫
          (skyscraperStalkIso b A).hom =
        (F.presheaf.germ U b hb ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map (toSkyscraper F b A φ).hom) ≫
          (skyscraperStalkIso b A).hom := (Category.assoc _ _ _).symm
    _ = ((toSkyscraper F b A φ).hom.app (op U) ≫
          (skyscraper b A).presheaf.germ U b hb) ≫ (skyscraperStalkIso b A).hom :=
      congrArg (fun k => k ≫ (skyscraperStalkIso b A).hom)
        (TopCat.Presheaf.stalkFunctor_map_germ U b hb (toSkyscraper F b A φ).hom)
    _ = (toSkyscraper F b A φ).hom.app (op U) ≫
          ((skyscraper b A).presheaf.germ U b hb ≫ (skyscraperStalkIso b A).hom) :=
      Category.assoc _ _ _
    _ = (toSkyscraper F b A φ).hom.app (op U) ≫
          (skyscraperSectionIso b A U hb).hom :=
      congrArg (fun k => (toSkyscraper F b A φ).hom.app (op U) ≫ k)
        (germ_skyscraperStalkIso_hom b A U hb)
    _ = F.presheaf.germ U b hb ≫ φ := toSkyscraper_app F b A φ U hb

/-- Morphisms into the skyscraper are determined by their actual
components on the neighborhoods of its support; all other components
land in terminal section groups. -/
theorem skyscraper_hom_ext {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {b : X} {A : AddCommGrpCat.{0}} {f g : F ⟶ skyscraper b A}
    (h : ∀ (U : Opens X) (hb : b ∈ U),
      f.hom.app (op U) ≫ (skyscraperSectionIso b A U hb).hom =
        g.hom.app (op U) ≫ (skyscraperSectionIso b A U hb).hom) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  by_cases hb : b ∈ U.unop
  · exact (cancel_mono (skyscraperSectionIso b A U.unop hb).hom).mp (h U.unop hb)
  · exact (skyscraperSectionIsTerminal b A U.unop hb).hom_ext _ _

/-- Constructing the skyscraper morphism is natural in its source:
precomposing a sheaf morphism is the same as precomposing its actual
stalk map. -/
theorem toSkyscraper_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (α : F ⟶ G) (b : X) (A : AddCommGrpCat.{0}) (φ : G.presheaf.stalk b ⟶ A) :
    α ≫ toSkyscraper G b A φ =
      toSkyscraper F b A ((TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map α.hom ≫ φ) := by
  apply skyscraper_hom_ext
  intro U hb
  change (α.hom.app (op U) ≫ (toSkyscraper G b A φ).hom.app (op U)) ≫ _ = _
  calc
    (α.hom.app (op U) ≫ (toSkyscraper G b A φ).hom.app (op U)) ≫
          (skyscraperSectionIso b A U hb).hom =
        α.hom.app (op U) ≫
          ((toSkyscraper G b A φ).hom.app (op U) ≫ (skyscraperSectionIso b A U hb).hom) :=
      Category.assoc _ _ _
    _ = α.hom.app (op U) ≫ G.presheaf.germ U b hb ≫ φ :=
      congrArg (fun k => α.hom.app (op U) ≫ k) (toSkyscraper_app G b A φ U hb)
    _ = F.presheaf.germ U b hb ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map α.hom ≫ φ :=
      (TopCat.Presheaf.stalkFunctor_map_germ_assoc U b hb α.hom φ).symm
    _ = (toSkyscraper F b A
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map α.hom ≫ φ)).hom.app (op U) ≫
          (skyscraperSectionIso b A U hb).hom :=
      (toSkyscraper_app F b A
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map α.hom ≫ φ) U hb).symm

end Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation
