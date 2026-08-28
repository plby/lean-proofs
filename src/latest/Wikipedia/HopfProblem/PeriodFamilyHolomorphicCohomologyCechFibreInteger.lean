import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardGlobal
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSheafBasic

/-!
# Canonical integer sections under actual pushforward

The canonical integer-sheaf map defined by the global-section adjunction
preserves the original constant-presheaf sections on every open set.
This identifies its degree map with the literal Čech degree map after
inverse image of opens.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechFibre

open CuspNormalization.SheafCohomologyFinitePushforward
open HolomorphicPicard.CechExtension

/-- The native constant-sheaf adjunction evaluates a map at its original
global constant section of degree one. -/
theorem homGlobalEquiv_degreeUnit (X : TopCat.{0}) (F : AbelianSheaf X)
    (h : integerSheaf X ⟶ F) :
    homGlobalEquiv X F h =
      h.hom.app (op (⊤ : Opens X))
        ((degreeUnit X).app (op (⊤ : Opens X)) (ULift.up (1 : ℤ))) := by
  rfl

variable {T X : TopCat.{0}} (f : T ⟶ X)

/-- The canonical integer map preserves the original global degree-one
section, with no assumptions on the continuous map. -/
theorem integerUnit_degreeUnit_top_one :
    (integerUnit f).hom.app (op (⊤ : Opens X))
        ((degreeUnit X).app (op (⊤ : Opens X)) (ULift.up (1 : ℤ))) =
      (degreeUnit T).app (op (⊤ : Opens T)) (ULift.up (1 : ℤ)) := by
  exact (homGlobalEquiv_degreeUnit X ((pushforward f).obj (integerSheaf T))
    (integerUnit f)).symm.trans
      ((homPushforwardEquiv_global f (integerSheaf T) (𝟙 _)).trans
        (homGlobalEquiv_degreeUnit T (integerSheaf T) (𝟙 _)))

/-- The canonical integer map preserves every original global constant
integer section. -/
theorem integerUnit_degreeUnit_top (n : ULift.{0} ℤ) :
    (integerUnit f).hom.app (op (⊤ : Opens X))
        ((degreeUnit X).app (op (⊤ : Opens X)) n) =
      (degreeUnit T).app (op (⊤ : Opens T)) n := by
  have h :
      (degreeUnit X).app (op (⊤ : Opens X)) ≫
          (integerUnit f).hom.app (op (⊤ : Opens X)) =
        (degreeUnit T).app (op (⊤ : Opens T)) := by
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
    exact integerUnit_degreeUnit_top_one f
  exact ConcreteCategory.congr_hom h n

/-- On every actual open set, the canonical integer-sheaf map sends the
original Čech degree section to the same degree on its inverse image. -/
theorem integerUnit_degreeUnit_app (V : Opens X) (n : ULift.{0} ℤ) :
    (integerUnit f).hom.app (op V) ((degreeUnit X).app (op V) n) =
      (degreeUnit T).app (op ((Opens.map f).obj V)) n := by
  let r : V ⟶ (⊤ : Opens X) := homOfLE le_top
  have hX := ConcreteCategory.congr_hom ((degreeUnit X).naturality r.op) n
  have hT := ConcreteCategory.congr_hom
    ((degreeUnit T).naturality ((Opens.map f).map r).op) n
  have hf := ConcreteCategory.congr_hom ((integerUnit f).hom.naturality r.op)
    ((degreeUnit X).app (op (⊤ : Opens X)) n)
  change (degreeUnit X).app (op V) n =
    (integerSheaf X).obj.map r.op ((degreeUnit X).app (op (⊤ : Opens X)) n) at hX
  rw [hX]
  exact hf.trans ((congrArg
    (((pushforward f).obj (integerSheaf T)).obj.map r.op)
    (integerUnit_degreeUnit_top f n)).trans hT.symm)

/-- The canonical integer map composed with the original degree unit is
the actual inverse-open-set whiskering of the original source degree unit. -/
theorem degreeUnit_integerUnit :
    degreeUnit X ≫ (integerUnit f).hom =
      Functor.whiskerLeft (Opens.map f).op (degreeUnit T) := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro n
  exact integerUnit_degreeUnit_app f V.unop n

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechFibre
