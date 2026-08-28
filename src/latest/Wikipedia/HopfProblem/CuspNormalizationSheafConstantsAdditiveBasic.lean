import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsBasic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits

/-!
# The actual additive constant complex sheaf

Forgetting the ring structure of the actual constant complex sheaf
commutes with sheafification.  Thus the resulting additive sheaf is
canonically isomorphic to Mathlib's constant additive sheaf with value
`ℂ`, without any extra constancy or preservation hypothesis.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

/-- The genuine constant additive presheaf with value `ℂ`. -/
def constantAdditivePresheaf (X : TopCat.{0}) : TopCat.Presheaf AddCommGrpCat.{0} X :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of ℂ)

/-- The additive sheaf obtained from the actual constant complex ring sheaf. -/
def complexAdditiveSheaf (X : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj
    (complexSheaf X)

/-- The ring-sheafification unit, with only its additive structure retained. -/
def additiveUnit (X : TopCat.{0}) :
    constantAdditivePresheaf X ⟶ (complexAdditiveSheaf X).obj :=
  Functor.whiskerRight (unit X) (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)

@[simp] theorem additiveUnit_app_apply (X : TopCat.{0}) (U : Opens X) (c : ℂ) :
    (additiveUnit X).app (op U) c = (unit X).app (op U) c := rfl

/-- Forgetting the actual constant ring sheaf gives the native constant
additive sheaf, via the canonical sheafification comparison. -/
def complexAdditiveSheafIso (X : TopCat.{0}) :
    complexAdditiveSheaf X ≅
      (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (AddCommGrpCat.of ℂ) :=
  (constantCommuteCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).app (CommRingCat.of ℂ)

/-- Complex scalars in the actual constant sheaf are given by its
sheafification unit on each open set. -/
instance complexSheaf_obj_algebra (X : TopCat.{0}) (U : (Opens X)ᵒᵖ) :
    Algebra ℂ ((complexSheaf X).obj.obj U) :=
  ((unit X).app U).hom.toAlgebra

@[simp] theorem complexSheaf_algebraMap_eq_unit (X : TopCat.{0})
    (U : (Opens X)ᵒᵖ) (c : ℂ) :
    algebraMap ℂ ((complexSheaf X).obj.obj U) c = (unit X).app U c := rfl

/-- The additive constant-sheaf sections retain this actual complex
module structure after forgetting multiplication. -/
instance complexAdditiveSheaf_obj_module (X : TopCat.{0}) (U : (Opens X)ᵒᵖ) :
    Module ℂ ((complexAdditiveSheaf X).obj.obj U) :=
  inferInstanceAs (Module ℂ ((complexSheaf X).obj.obj U))

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
