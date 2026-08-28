import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySkyscraper
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# The actual product-of-stalks injective presentation

This constructs the first Godement term as a genuine product of genuine
skyscraper sheaves, and its natural map from a given abelian sheaf. The
actual stalk-skyscraper adjunction proves injectivity of this map on every
stalk. If the actual stalk groups are injective, the product is an actual
injective object, hence gives an actual injective presentation and its
canonical cokernel short exact sequence.

These constructions do not assert analytic acyclicity of the toric
surface. They retain the genuine sheaf objects needed for that proof.
-/

noncomputable section

open TopCat CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Godement

attribute [local instance] Classical.propDecidable

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)

/-- The actual skyscraper containing the germs at one point. -/
abbrev pointTerm (x : X) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  skyscraperSheaf x (F.presheaf.stalk x)

/-- The first actual Godement term, as a categorical product. -/
abbrev sheaf : TopCat.Sheaf AddCommGrpCat.{0} X := ∏ᶜ (pointTerm F)

/-- The canonical map records the actual germ at every point. -/
def inclusion : F ⟶ sheaf F :=
  Pi.lift fun x => (stalkSkyscraperSheafAdjunction x).unit.app F

@[reassoc] theorem inclusion_component (x : X) :
    inclusion F ≫ Pi.π (pointTerm F) x =
      (stalkSkyscraperSheafAdjunction x).unit.app F :=
  Pi.lift_π _ _

/-- Evaluation at the same point is a left inverse to the actual germ
inclusion after taking its stalk. -/
theorem stalk_inclusion_retraction (x : X) :
    (CuspNormalization.SheafBiproduct.stalkFunctor X x).map (inclusion F) ≫
      ((CuspNormalization.SheafBiproduct.stalkFunctor X x).map
          (Pi.π (pointTerm F) x) ≫
        (stalkSkyscraperSheafAdjunction x).counit.app (F.presheaf.stalk x)) =
      𝟙 (F.presheaf.stalk x) := by
  let K := CuspNormalization.SheafBiproduct.stalkFunctor X x
  have hmap : K.map (inclusion F) ≫ K.map (Pi.π (pointTerm F) x) =
      K.map ((stalkSkyscraperSheafAdjunction x).unit.app F) :=
    (K.map_comp _ _).symm.trans (congrArg K.map (inclusion_component F x))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m : K.obj F ⟶ K.obj (pointTerm F x) => m ≫
      (stalkSkyscraperSheafAdjunction x).counit.app (K.obj F)) hmap).trans
        ((stalkSkyscraperSheafAdjunction x).left_triangle_components F))

/-- The canonical product-of-germs map is a monomorphism of genuine sheaves. -/
instance inclusion_mono : Mono (inclusion F) := by
  apply (TopCat.Presheaf.mono_iff_stalk_mono (inclusion F)).mpr
  intro x
  let K := CuspNormalization.SheafBiproduct.stalkFunctor X x
  have h : K.map (inclusion F) ≫
      (K.map (Pi.π (pointTerm F) x) ≫
        (stalkSkyscraperSheafAdjunction x).counit.app (K.obj F)) = 𝟙 (K.obj F) :=
    stalk_inclusion_retraction F x
  change Mono (K.map (inclusion F))
  apply ConcreteCategory.mono_of_injective
  intro a b hab
  let r : K.obj (sheaf F) ⟶ K.obj F := K.map (Pi.π (pointTerm F) x) ≫
    (stalkSkyscraperSheafAdjunction x).counit.app (K.obj F)
  exact (ConcreteCategory.congr_hom h a).symm.trans
    ((congrArg r hab).trans (ConcreteCategory.congr_hom h b))

/-- Injective actual stalk groups give an injective actual Godement term. -/
theorem sheaf_injective (hF : ∀ x : X, Injective (F.presheaf.stalk x)) :
    Injective (sheaf F) := by
  let h (x : X) : Injective (pointTerm F x) := by
    let := hF x
    exact CuspNormalization.SheafCohomology.skyscraper_injective x (F.presheaf.stalk x)
  exact inferInstanceAs (Injective (∏ᶜ (pointTerm F)))

/-- The constructed actual injective presentation, not a replacement
for the definition of sheaf cohomology. -/
def presentation (hF : ∀ x : X, Injective (F.presheaf.stalk x)) :
    InjectivePresentation F where
  J := sheaf F
  injective := sheaf_injective F hF
  f := inclusion F

/-- Its canonical cokernel sequence is genuinely short exact. -/
theorem presentation_shortExact (hF : ∀ x : X, Injective (F.presheaf.stalk x)) :
    (presentation F hF).shortComplex.ShortExact :=
  (presentation F hF).shortExact_shortComplex

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Godement
