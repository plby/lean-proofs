import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsBasic
import Mathlib.Topology.Sheaves.Functors

/-!
# Naturality of the actual constant sheaf under continuous pullback

A continuous map gives an actual morphism from the constant sheaf on its
target to the pushforward of the constant sheaf on its source.  The map
sends a constant representative to the same complex number on the actual
inverse-image open set.  The resulting square with maps to other sheaves
commutes as soon as their literal constant representatives commute.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {X Y : TopCat.{0}}

/-- Constants pull back to the same constants on actual inverse-image opens. -/
def pullbackPresheafMap (f : X ⟶ Y) : constantPresheaf Y ⟶
    ((TopCat.Sheaf.pushforward CommRingCat f).obj (complexSheaf X)).obj where
  app U := (unit X).app (op ((Opens.map f).obj U.unop))
  naturality _ _ h := (unit X).naturality ((Opens.map f).map h.unop).op

/-- The actual contravariant constant-sheaf map, expressed as a morphism
to the genuine sheaf pushforward. -/
def pullbackMap (f : X ⟶ Y) : complexSheaf Y ⟶
    (TopCat.Sheaf.pushforward CommRingCat f).obj (complexSheaf X) :=
  lift ((TopCat.Sheaf.pushforward CommRingCat f).obj (complexSheaf X))
    (pullbackPresheafMap f)

@[simp] theorem pullbackMap_unit (f : X ⟶ Y) (U : Opens Y) (c : ℂ) :
    (pullbackMap f).hom.app (op U) ((unit Y).app (op U) c) =
      (unit X).app (op ((Opens.map f).obj U)) c :=
  lift_app_unit _ (pullbackPresheafMap f) U c

/-- The constant-sheaf square commutes for any actual target pullback
that preserves the specified constant complex sections. -/
theorem pullback_naturality (f : X ⟶ Y) (FX : RingSheaf X) (FY : RingSheaf Y)
    (φX : constantPresheaf X ⟶ FX.obj) (φY : constantPresheaf Y ⟶ FY.obj)
    (p : FY ⟶ (TopCat.Sheaf.pushforward CommRingCat f).obj FX)
    (h : ∀ (U : Opens Y) (c : ℂ),
      p.hom.app (op U) (φY.app (op U) c) =
        φX.app (op ((Opens.map f).obj U)) c) :
    lift FY φY ≫ p = pullbackMap f ≫
      (TopCat.Sheaf.pushforward CommRingCat f).map (lift FX φX) := by
  apply hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change p.hom.app U ((lift FY φY).hom.app U ((unit Y).app U c)) =
    (lift FX φX).hom.app (op ((Opens.map f).obj U.unop))
      ((pullbackMap f).hom.app U ((unit Y).app U c))
  exact (congrArg (p.hom.app U) (lift_app_unit FY φY U.unop c)).trans
    ((h U.unop c).trans
      ((lift_app_unit FX φX ((Opens.map f).obj U.unop) c).symm.trans
        (congrArg ((lift FX φX).hom.app (op ((Opens.map f).obj U.unop)))
          (pullbackMap_unit f U.unop c).symm)))

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
