import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Topology.Sheaves.Sheaf

/-!
# The actual constant additive integer sheaf

The integer sheaf is Mathlib's sheafification of the constant additive
integer presheaf. Its sections are not required to be globally constant
on disconnected opens. The sheafification unit and universal property
give the genuine maps out of this sheaf used by the exponential sequence.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

abbrev IntegerAdditiveSheaf (X : TopCat.{0}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

/-- The actual constant presheaf with additive value `ℤ`. -/
def integerPresheaf (X : TopCat.{0}) : TopCat.Presheaf AddCommGrpCat.{0} X :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of ℤ)

/-- The native sheafified constant integer sheaf. -/
def integerSheaf (X : TopCat.{0}) : IntegerAdditiveSheaf X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of ℤ)

/-- The genuine sheafification map, not a replacement by global constants. -/
def integerUnit (X : TopCat.{0}) : integerPresheaf X ⟶ (integerSheaf X).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) (integerPresheaf X)

@[simp] theorem integerUnit_app (X : TopCat.{0}) (U : Opens X) (n : ℤ) :
    (integerUnit X).app (op U) n =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (integerPresheaf X)).app (op U) n := rfl

/-- A constant representative restricts to the same integer representative. -/
theorem integerUnit_restrict {X : TopCat.{0}} {U V : Opens X} (hVU : V ≤ U) (n : ℤ) :
    (integerSheaf X).obj.map (homOfLE hVU).op ((integerUnit X).app (op U) n) =
      (integerUnit X).app (op V) n := by
  exact (ConcreteCategory.congr_hom ((integerUnit X).naturality (homOfLE hVU).op) n).symm

/-- The universal extension of compatible literal integer sections. -/
def integerLift {X : TopCat.{0}} (F : IntegerAdditiveSheaf X)
    (φ : integerPresheaf X ⟶ F.obj) : integerSheaf X ⟶ F where
  hom := CategoryTheory.sheafifyLift (Opens.grothendieckTopology X) φ F.property

theorem integerUnit_lift {X : TopCat.{0}} (F : IntegerAdditiveSheaf X)
    (φ : integerPresheaf X ⟶ F.obj) :
    integerUnit X ≫ (integerLift F φ).hom = φ :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology X) φ F.property

@[simp] theorem integerLift_app_unit {X : TopCat.{0}} (F : IntegerAdditiveSheaf X)
    (φ : integerPresheaf X ⟶ F.obj) (U : Opens X) (n : ℤ) :
    (integerLift F φ).hom.app (op U) ((integerUnit X).app (op U) n) = φ.app (op U) n :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (integerUnit_lift F φ) (op U)) n

/-- Maps from the actual integer sheaf are determined on the genuine unit. -/
theorem integerHom_ext {X : TopCat.{0}} {F : IntegerAdditiveSheaf X}
    {f g : integerSheaf X ⟶ F}
    (h : integerUnit X ≫ f.hom = integerUnit X ≫ g.hom) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology X)
    f.hom g.hom F.property h

/-- Sectionwise constant representatives suffice for equality of actual sheaf maps. -/
theorem integerHom_ext_on_constants {X : TopCat.{0}} {F : IntegerAdditiveSheaf X}
    {f g : integerSheaf X ⟶ F}
    (h : ∀ (U : Opens X) (n : ℤ),
      f.hom.app (op U) ((integerUnit X).app (op U) n) =
        g.hom.app (op U) ((integerUnit X).app (op U) n)) : f = g := by
  apply integerHom_ext
  ext U n
  exact h U n

theorem integerLift_comp {X : TopCat.{0}} (F G : IntegerAdditiveSheaf X)
    (φ : integerPresheaf X ⟶ F.obj) (ψ : F ⟶ G) :
    integerLift F φ ≫ ψ = integerLift G (φ ≫ ψ.hom) := by
  apply integerHom_ext
  change integerUnit X ≫ (integerLift F φ).hom ≫ ψ.hom =
    integerUnit X ≫ (integerLift G (φ ≫ ψ.hom)).hom
  rw [← Category.assoc, integerUnit_lift, integerUnit_lift]

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
