import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Topology.Sheaves.Sheaf

/-!
# Native constant additive sheaves

These definitions retain Mathlib's actual sheafification of the constant
presheaf.  In particular a section on a disconnected open set is not required
to have just one value.  The coefficient is an arbitrary small abelian group.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Constant

abbrev AdditiveSheaf (X : TopCat.{0}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

/-- The actual constant presheaf with coefficient group `A`. -/
def presheaf (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    TopCat.Presheaf AddCommGrpCat.{0} X :=
  (Functor.const (Opens X)ᵒᵖ).obj A

/-- Mathlib's native constant additive sheaf. -/
def sheaf (X : TopCat.{0}) (A : AddCommGrpCat.{0}) : AdditiveSheaf X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj A

/-- The actual sheafification unit, which sends values to constant sections. -/
def unit (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    presheaf X A ⟶ (sheaf X A).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) (presheaf X A)

/-- Restricting a genuine constant section keeps its original value. -/
@[simp]
theorem unit_restrict (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    {U V : Opens X} (i : V ⟶ U) (a : A) :
    (sheaf X A).obj.map i.op ((unit X A).app (op U) a) =
      (unit X A).app (op V) a := by
  exact (ConcreteCategory.congr_hom ((unit X A).naturality i.op) a).symm

/-- Compatible assignments on the constant presheaf extend to the native
constant sheaf by the sheafification universal property. -/
def lift {X : TopCat.{0}} {A : AddCommGrpCat.{0}} (F : AdditiveSheaf X)
    (φ : presheaf X A ⟶ F.obj) : sheaf X A ⟶ F where
  hom := CategoryTheory.sheafifyLift (Opens.grothendieckTopology X) φ F.property

theorem unit_lift {X : TopCat.{0}} {A : AddCommGrpCat.{0}} (F : AdditiveSheaf X)
    (φ : presheaf X A ⟶ F.obj) :
    unit X A ≫ (lift F φ).hom = φ :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology X) φ F.property

@[simp]
theorem lift_app_unit {X : TopCat.{0}} {A : AddCommGrpCat.{0}}
    (F : AdditiveSheaf X) (φ : presheaf X A ⟶ F.obj) (U : Opens X) (a : A) :
    (lift F φ).hom.app (op U) ((unit X A).app (op U) a) = φ.app (op U) a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (unit_lift F φ) (op U)) a

/-- Equality on the original constant representatives determines a sheaf map. -/
theorem hom_ext {X : TopCat.{0}} {A : AddCommGrpCat.{0}} {F : AdditiveSheaf X}
    {f g : sheaf X A ⟶ F}
    (h : unit X A ≫ f.hom = unit X A ≫ g.hom) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology X)
    f.hom g.hom F.property h

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Constant
