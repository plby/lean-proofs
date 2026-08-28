import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Group.Hom.Instances

/-!
# Additive pairings into the original categorical kernel

If a given additive pairing is killed by an actual group morphism,
the categorical kernel lift gives a pairing into its actual kernel.
The original kernel inclusion recovers the given pairing literally.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProduct.Cusp

variable {A B D : AddCommGrpCat.{0}} (f : B ⟶ D) (p : A →+ A →+ B)
  (h : ∀ a b, f (p a b) = 0)

/-- The original right-hand additive map lifted through the categorical kernel. -/
def kernelPairingRight (a : A) : A →+ (kernel f : AddCommGrpCat.{0}) :=
  (kernel.lift f (AddCommGrpCat.ofHom (p a)) (by ext b; exact h a b)).hom

theorem kernelPairingRight_ι (a b : A) :
    kernel.ι f (kernelPairingRight f p h a b) = p a b :=
  ConcreteCategory.congr_hom
    (kernel.lift_ι f (AddCommGrpCat.ofHom (p a)) (by ext t; exact h a t)) b

/-- The genuine categorical kernel lift is additive in both arguments. -/
def kernelPairing : A →+ A →+ (kernel f : AddCommGrpCat.{0}) where
  toFun := kernelPairingRight f p h
  map_zero' := by
    ext b
    apply AddCommGrpCat.injective_of_mono (kernel.ι f)
    change kernel.ι f (kernelPairingRight f p h 0 b) = kernel.ι f 0
    simp only [kernelPairingRight_ι, map_zero, AddMonoidHom.zero_apply]
  map_add' a a' := by
    ext b
    apply AddCommGrpCat.injective_of_mono (kernel.ι f)
    change kernel.ι f (kernelPairingRight f p h (a + a') b) =
      kernel.ι f (kernelPairingRight f p h a b + kernelPairingRight f p h a' b)
    simp only [kernelPairingRight_ι, map_add, AddMonoidHom.add_apply]

/-- The kernel inclusion retains the original bilinear class, not a replacement. -/
theorem kernelPairing_ι (a b : A) : kernel.ι f (kernelPairing f p h a b) = p a b :=
  kernelPairingRight_ι f p h a b

end Wikipedia.HopfProblem.SheafCupProduct.Cusp
