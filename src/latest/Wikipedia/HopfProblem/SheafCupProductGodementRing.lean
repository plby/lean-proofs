import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyGodementFunctor
import Wikipedia.HopfProblem.CuspNormalizationSheafForgetStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsBasic

/-!
# The multiplicative product-of-stalks construction

The first Godement term of an actual commutative-ring sheaf is the
categorical product of its actual stalk skyscrapers.  The germ inclusion
and its functoriality are ring morphisms.  At each actual stalk, evaluation
at that same point is a natural retraction of the germ inclusion.  These
are the maps used in the multiplicative resolution, not a prescribed
cohomology complex.
-/

noncomputable section

open TopCat CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.SheafCupProduct.GodementRing

attribute [local instance] Classical.propDecidable

abbrev RingSheaf (X : TopCat.{0}) := TopCat.Sheaf CommRingCat.{0} X

variable {X : TopCat.{0}}

/-- The actual ring-valued stalk functor. -/
abbrev stalk (x : X) : RingSheaf X ⥤ CommRingCat.{0} :=
  TopCat.Sheaf.forget CommRingCat X ⋙ TopCat.Presheaf.stalkFunctor CommRingCat x

/-- The actual skyscraper with the original ring-valued stalk. -/
abbrev pointTerm (F : RingSheaf X) (x : X) : RingSheaf X :=
  skyscraperSheaf x (F.presheaf.stalk x)

/-- The multiplicative Godement term is an actual sheaf product. -/
abbrev sheaf (F : RingSheaf X) : RingSheaf X := ∏ᶜ (pointTerm F)

/-- Each component of this map is the original germ map. -/
def inclusion (F : RingSheaf X) : F ⟶ sheaf F :=
  Pi.lift fun x => (stalkSkyscraperSheafAdjunction x).unit.app F

@[reassoc] theorem inclusion_component (F : RingSheaf X) (x : X) :
    inclusion F ≫ Pi.π (pointTerm F) x =
      (stalkSkyscraperSheafAdjunction x).unit.app F :=
  Pi.lift_π _ _

/-- Ring morphisms act on the original stalk and its skyscraper. -/
def pointMap {F G : RingSheaf X} (f : F ⟶ G) (x : X) :
    pointTerm F x ⟶ pointTerm G x :=
  (skyscraperSheafFunctor (C := CommRingCat.{0}) x).map ((stalk x).map f)

/-- The actual product map on multiplicative Godement terms. -/
def map {F G : RingSheaf X} (f : F ⟶ G) : sheaf F ⟶ sheaf G :=
  Pi.lift fun x => Pi.π (pointTerm F) x ≫ pointMap f x

@[reassoc] theorem map_component {F G : RingSheaf X} (f : F ⟶ G) (x : X) :
    map f ≫ Pi.π (pointTerm G) x = Pi.π (pointTerm F) x ≫ pointMap f x :=
  Pi.lift_π _ _

@[simp] theorem pointMap_id (F : RingSheaf X) (x : X) :
    pointMap (𝟙 F) x = 𝟙 (pointTerm F x) := by
  let S := skyscraperSheafFunctor (C := CommRingCat.{0}) x
  exact (congrArg S.map ((stalk x).map_id F)).trans (S.map_id ((stalk x).obj F))

theorem pointMap_comp {F G H : RingSheaf X} (f : F ⟶ G) (g : G ⟶ H) (x : X) :
    pointMap (f ≫ g) x = pointMap f x ≫ pointMap g x := by
  let S := skyscraperSheafFunctor (C := CommRingCat.{0}) x
  exact (congrArg S.map ((stalk x).map_comp f g)).trans
    (S.map_comp ((stalk x).map f) ((stalk x).map g))

@[simp] theorem map_id (F : RingSheaf X) : map (𝟙 F) = 𝟙 (sheaf F) := by
  apply Pi.hom_ext
  intro x
  rw [map_component, pointMap_id, Category.comp_id, Category.id_comp]

theorem map_comp {F G H : RingSheaf X} (f : F ⟶ G) (g : G ⟶ H) :
    map (f ≫ g) = map f ≫ map g := by
  apply Pi.hom_ext
  intro x
  simp only [map_component, map_component_assoc, pointMap_comp, Category.assoc]

/-- The genuine multiplicative product-of-stalks functor. -/
def functor : RingSheaf X ⥤ RingSheaf X where
  obj := sheaf
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The actual germ inclusion is natural as a ring-sheaf map. -/
theorem inclusion_naturality {F G : RingSheaf X} (f : F ⟶ G) :
    inclusion F ≫ map f = f ≫ inclusion G := by
  apply Pi.hom_ext
  intro x
  rw [Category.assoc, map_component, ← Category.assoc, inclusion_component,
    Category.assoc, inclusion_component]
  exact ((stalkSkyscraperSheafAdjunction x).unit.naturality f).symm

/-- The natural transformation which inserts actual section germs. -/
def unit : 𝟭 (RingSheaf X) ⟶ functor where
  app := inclusion
  naturality _ _ f := (inclusion_naturality f).symm

/-- Evaluation at the selected point, after taking its genuine stalk. -/
def retraction (F : RingSheaf X) (x : X) :
    (stalk x).obj (sheaf F) ⟶ (stalk x).obj F :=
  (stalk x).map (Pi.π (pointTerm F) x) ≫
    (stalkSkyscraperSheafAdjunction x).counit.app ((stalk x).obj F)

/-- The actual ring-valued stalk evaluation retracts the germ insertion. -/
@[reassoc] theorem inclusion_retraction (F : RingSheaf X) (x : X) :
    (stalk x).map (inclusion F) ≫ retraction F x = 𝟙 ((stalk x).obj F) := by
  let K := stalk x
  have hmap : K.map (inclusion F) ≫ K.map (Pi.π (pointTerm F) x) =
      K.map ((stalkSkyscraperSheafAdjunction x).unit.app F) :=
    (K.map_comp _ _).symm.trans (congrArg K.map (inclusion_component F x))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m : K.obj F ⟶ K.obj (pointTerm F x) => m ≫
      (stalkSkyscraperSheafAdjunction x).counit.app (K.obj F)) hmap).trans
        ((stalkSkyscraperSheafAdjunction x).left_triangle_components F))

/-- The retraction commutes with every original stalk map. -/
@[reassoc] theorem retraction_naturality {F G : RingSheaf X} (f : F ⟶ G) (x : X) :
    (stalk x).map (map f) ≫ retraction G x = retraction F x ≫ (stalk x).map f := by
  let K := stalk x
  let eF : K.obj (pointTerm F x) ⟶ K.obj F :=
    (stalkSkyscraperSheafAdjunction x).counit.app (K.obj F)
  let eG : K.obj (pointTerm G x) ⟶ K.obj G :=
    (stalkSkyscraperSheafAdjunction x).counit.app (K.obj G)
  have hmap : K.map (map f) ≫ K.map (Pi.π (pointTerm G) x) =
      K.map (Pi.π (pointTerm F) x) ≫ K.map (pointMap f x) :=
    (K.map_comp _ _).symm.trans
      ((congrArg K.map (map_component f x)).trans (K.map_comp _ _))
  have he : K.map (pointMap f x) ≫ eG = eF ≫ K.map f :=
    (stalkSkyscraperSheafAdjunction x).counit.naturality (K.map f)
  change K.map (map f) ≫ (K.map (Pi.π (pointTerm G) x) ≫ eG) =
    (K.map (Pi.π (pointTerm F) x) ≫ eF) ≫ K.map f
  calc
    K.map (map f) ≫ (K.map (Pi.π (pointTerm G) x) ≫ eG) =
        (K.map (map f) ≫ K.map (Pi.π (pointTerm G) x)) ≫ eG :=
      (Category.assoc _ _ _).symm
    _ = (K.map (Pi.π (pointTerm F) x) ≫ K.map (pointMap f x)) ≫ eG :=
      congrArg (fun m => m ≫ eG) hmap
    _ = K.map (Pi.π (pointTerm F) x) ≫ (K.map (pointMap f x) ≫ eG) :=
      Category.assoc _ _ _
    _ = K.map (Pi.π (pointTerm F) x) ≫ (eF ≫ K.map f) :=
      congrArg (fun m => K.map (Pi.π (pointTerm F) x) ≫ m) he
    _ = (K.map (Pi.π (pointTerm F) x) ≫ eF) ≫ K.map f :=
      (Category.assoc _ _ _).symm

end Wikipedia.HopfProblem.SheafCupProduct.GodementRing
