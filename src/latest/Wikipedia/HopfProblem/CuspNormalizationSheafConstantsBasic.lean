import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Analysis.Complex.Basic

/-!
# The actual constant complex sheaf

The constant complex sheaf is Mathlib's sheafification of the constant
complex presheaf.  It is not the presheaf of globally constant functions:
on a disconnected open set its sections may have different local values.
The universal property constructs its canonical maps into genuine sheaves
and proves their naturality before any choice of analytic target.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

/-- The native category of commutative-ring sheaves on a small space. -/
abbrev RingSheaf (X : TopCat.{0}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}

/-- The genuine constant presheaf with value `ℂ`. -/
def constantPresheaf (X : TopCat.{0}) : TopCat.Presheaf CommRingCat.{0} X :=
  (Functor.const (Opens X)ᵒᵖ).obj (CommRingCat.of ℂ)

/-- The actual constant complex sheaf, obtained by sheafification. -/
def complexSheaf (X : TopCat.{0}) : RingSheaf X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) CommRingCat.{0}).obj
    (CommRingCat.of ℂ)

/-- The canonical map from constant values to their sheafified sections. -/
def unit (X : TopCat.{0}) : constantPresheaf X ⟶ (complexSheaf X).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) (constantPresheaf X)

/-- A compatible assignment of literal constants extends uniquely from
the constant presheaf to the actual constant sheaf. -/
def lift {X : TopCat.{0}} (F : RingSheaf X)
    (φ : constantPresheaf X ⟶ F.obj) : complexSheaf X ⟶ F where
  hom := CategoryTheory.sheafifyLift (Opens.grothendieckTopology X) φ F.property

/-- The extension sends every constant representative to its specified section. -/
theorem unit_lift {X : TopCat.{0}} (F : RingSheaf X)
    (φ : constantPresheaf X ⟶ F.obj) :
    unit X ≫ (lift F φ).hom = φ :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology X) φ F.property

@[simp] theorem lift_app_unit {X : TopCat.{0}} (F : RingSheaf X)
    (φ : constantPresheaf X ⟶ F.obj) (U : Opens X) (c : ℂ) :
    (lift F φ).hom.app (op U) ((unit X).app (op U) c) = φ.app (op U) c := by
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (unit_lift F φ) (op U)) c

/-- Maps out of the actual constant sheaf are determined by their action
on constant presheaf representatives. -/
theorem hom_ext {X : TopCat.{0}} {F : RingSheaf X}
    {f g : complexSheaf X ⟶ F}
    (h : unit X ≫ f.hom = unit X ≫ g.hom) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology X)
    f.hom g.hom F.property h

/-- Naturality of the extension with respect to actual target-sheaf maps. -/
theorem lift_comp {X : TopCat.{0}} (F G : RingSheaf X)
    (φ : constantPresheaf X ⟶ F.obj) (ψ : F ⟶ G) :
    lift F φ ≫ ψ = lift G (φ ≫ ψ.hom) := by
  apply hom_ext
  change unit X ≫ (lift F φ).hom ≫ ψ.hom = unit X ≫ (lift G (φ ≫ ψ.hom)).hom
  rw [← Category.assoc, unit_lift, unit_lift]

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
