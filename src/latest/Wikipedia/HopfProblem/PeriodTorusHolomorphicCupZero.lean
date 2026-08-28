import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupPairSheaf

/-!
# The actual zero third-form sheaf

The coefficient group on every open is literally the one-element
group. Its comparison with the chosen categorical zero object is
proved, so the low-degree comparison does not add fictitious forms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ZeroObject

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup

/-- The literal presheaf of zero coefficients. -/
def zeroPresheaf (X : TopCat.{0}) : TopCat.Presheaf AddCommGrpCat.{0} X where
  obj _ := AddCommGrpCat.of PUnit
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := rfl

instance zeroPresheaf_obj_subsingleton (X : TopCat.{0}) (U : (Opens X)ᵒᵖ) :
    Subsingleton ((zeroPresheaf X).obj U) := inferInstanceAs (Subsingleton PUnit)

/-- Every matching family of zero coefficients has its unique zero gluing. -/
theorem zeroPresheaf_isSheaf (X : TopCat.{0}) : (zeroPresheaf X).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (zeroPresheaf X)).mpr
  intro ι U s hs
  exact ⟨PUnit.unit, fun _ => Subsingleton.elim _ _,
    fun _ _ => Subsingleton.elim _ _⟩

/-- The actual zero sheaf, with literal trivial section groups. -/
def zeroSheaf (X : TopCat.{0}) : Pairs.AbSheaf X :=
  ⟨zeroPresheaf X, zeroPresheaf_isSheaf X⟩

instance zeroSheaf_obj_subsingleton (X : TopCat.{0}) (U : (Opens X)ᵒᵖ) :
    Subsingleton ((zeroSheaf X).obj.obj U) := inferInstanceAs (Subsingleton PUnit)

/-- This literal sheaf is genuinely a zero object. -/
theorem zeroSheaf_isZero (X : TopCat.{0}) : IsZero (zeroSheaf X) := by
  apply (IsZero.iff_id_eq_zero (zeroSheaf X)).mpr
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext fun _ => Subsingleton.elim _ _

/-- Comparison with the original chosen categorical zero object. -/
def zeroSheafIso (X : TopCat.{0}) : zeroSheaf X ≅ 0 :=
  (zeroSheaf_isZero X).isoZero

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup
