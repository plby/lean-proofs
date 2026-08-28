import Wikipedia.HopfProblem.CuspNormalizationSheafForgetStalkBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafFiniteStalk
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Additive sheaves and finite pushforward stalks of ring-valued sheaves

Forgetting the ring structure uses the actual sheaf-composition functor.
The resulting presheaf is definitionally the original presheaf composed
with the forgetful functor. Its stalks therefore have the canonical
filtered-colimit comparison with the original ring-valued stalks.

Combining this comparison with the proved finite-fibre formula gives an
additive equivalence from the actual additive pushforward stalk to the
product of the actual ring-valued stalks at the points of the fibre.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafForgetStalk

variable {X Y : TopCat.{0}}

/-- The actual additive sheaf obtained by forgetting the commutative
ring structure, using the existing sheaf-composition functor. -/
def additiveSheaf (F : TopCat.Sheaf CommRingCat.{0} X) :
    TopCat.Sheaf AddCommGrpCat.{0} X :=
  (sheafCompose (Opens.grothendieckTopology X) forgetToAdd).obj F

/-- The underlying presheaf is literally the composite forgetful
presheaf; no replacement of its sections or restriction maps is made. -/
@[simp] theorem additiveSheaf_presheaf (F : TopCat.Sheaf CommRingCat.{0} X) :
    (additiveSheaf F).presheaf = additivePresheaf F.presheaf := rfl

/-- The actual additive stalk of a ring-valued sheaf is canonically the
additive group of its actual ring-valued stalk. -/
def sheafStalkAddEquiv (F : TopCat.Sheaf CommRingCat.{0} X) (x : X) :
    (additiveSheaf F).presheaf.stalk x ≃+ F.presheaf.stalk x :=
  stalkAddEquiv F.presheaf x

/-- The sheaf stalk comparison preserves actual section germs. -/
@[simp] theorem sheafStalkAddEquiv_germ (F : TopCat.Sheaf CommRingCat.{0} X)
    (U : Opens X) (x : X) (hx : x ∈ U) (s : F.presheaf.obj (op U)) :
    sheafStalkAddEquiv F x ((additiveSheaf F).presheaf.germ U x hx s) =
      F.presheaf.germ U x hx s :=
  stalkAddEquiv_germ F.presheaf U x hx s

/-- The inverse comparison also preserves the same actual section
representatives. -/
@[simp] theorem sheafStalkAddEquiv_symm_germ (F : TopCat.Sheaf CommRingCat.{0} X)
    (U : Opens X) (x : X) (hx : x ∈ U) (s : F.presheaf.obj (op U)) :
    (sheafStalkAddEquiv F x).symm (F.presheaf.germ U x hx s) =
      (additiveSheaf F).presheaf.germ U x hx s :=
  stalkAddEquiv_symm_germ F.presheaf U x hx s

variable [T2Space X]

/-- For a closed map with finite fibre and Hausdorff source, the actual
additive pushforward stalk is canonically the product of the additive
groups of the original ring-valued stalks at the fibre points. -/
def pushforwardStalkAddEquiv (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf CommRingCat.{0} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) :
    (f _* (additiveSheaf F).presheaf).stalk y ≃+
      ∀ x : f ⁻¹' {y}, F.presheaf.stalk x.val :=
  (SheafFiniteStalk.pushforwardStalkEquiv f hf (additiveSheaf F) y hfinite).trans
    (AddEquiv.piCongrRight fun x => sheafStalkAddEquiv F x.val)

/-- Each component is the actual pushforward-stalk map followed by the
canonical forgetful stalk comparison. -/
@[simp] theorem pushforwardStalkAddEquiv_apply (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf CommRingCat.{0} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite)
    (s : (f _* (additiveSheaf F).presheaf).stalk y) (x : f ⁻¹' {y}) :
    pushforwardStalkAddEquiv f hf F y hfinite s x =
      sheafStalkAddEquiv F x.val
        (SheafFiniteStalk.pushforwardStalkComponent f (additiveSheaf F).presheaf y x s) :=
  rfl

/-- On a section over an inverse image, the composite equivalence gives
its actual ring-valued germs at every point of the fibre. -/
@[simp] theorem pushforwardStalkAddEquiv_germ (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf CommRingCat.{0} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) (U : Opens Y) (hy : y ∈ U)
    (s : F.presheaf.obj (op ((Opens.map f).obj U))) (x : f ⁻¹' {y}) :
    pushforwardStalkAddEquiv f hf F y hfinite
        ((f _* (additiveSheaf F).presheaf).germ U y hy s) x =
      F.presheaf.germ ((Opens.map f).obj U) x.val
        (SheafFiniteStalk.fiber_mem_preimage f y x U hy) s := by
  exact (congrArg (sheafStalkAddEquiv F x.val)
    (SheafFiniteStalk.pushforwardStalkComponent_germ f
      (additiveSheaf F).presheaf y x U hy s)).trans
    (sheafStalkAddEquiv_germ F ((Opens.map f).obj U) x.val
      (SheafFiniteStalk.fiber_mem_preimage f y x U hy) s)

end Wikipedia.HopfProblem.CuspNormalization.SheafForgetStalk
