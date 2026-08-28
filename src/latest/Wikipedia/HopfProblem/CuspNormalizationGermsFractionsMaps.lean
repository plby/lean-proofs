import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Group.Pi.Units

/-!
# The actual coordinate map into branch fraction rings

The product map is the coordinatewise canonical fraction-ring map. Its
algebra structure, and the induced algebra over any subring of the
original product, therefore use the actual inclusions. Injectivity uses
only the canonical injectivity of a ring into its total fraction ring.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.CuspNormalization.GermsFractions

universe u v

variable {I : Type u} (B : I → Type v) [∀ i, CommRing (B i)]

/-- The coordinatewise canonical map into the actual fraction rings. -/
def productFractionMap : (∀ i, B i) →+* ∀ i, FractionRing (B i) :=
  RingHom.pi fun i => (algebraMap (B i) (FractionRing (B i))).comp (Pi.evalRingHom B i)

@[simp] theorem productFractionMap_apply (b : ∀ i, B i) (i : I) :
    productFractionMap B b i = algebraMap (B i) (FractionRing (B i)) (b i) := rfl

theorem productFractionMap_injective : Injective (productFractionMap B) := by
  intro b c h
  funext i
  exact IsFractionRing.injective (B i) (FractionRing (B i)) (congrFun h i)

/-- The algebra structure is induced by the coordinatewise fraction map.
It is exposed as a reducible non-instance to make the scalar map explicit. -/
abbrev productFractionAlgebra : Algebra (∀ i, B i) (∀ i, FractionRing (B i)) :=
  (productFractionMap B).toAlgebra

attribute [local instance] productFractionAlgebra

/-- The resulting algebra map of a subring is the literal restriction of
the canonical coordinatewise fraction map. -/
@[simp] theorem subring_algebraMap_apply (A : Subring (∀ i, B i)) (a : A) (i : I) :
    algebraMap A (∀ i, FractionRing (B i)) a i =
      algebraMap (B i) (FractionRing (B i)) ((a : ∀ j, B j) i) := rfl

theorem subring_algebraMap_injective (A : Subring (∀ i, B i)) :
    Injective (algebraMap A (∀ i, FractionRing (B i))) :=
  (productFractionMap_injective B).comp Subtype.val_injective

end Wikipedia.HopfProblem.CuspNormalization.GermsFractions
