import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtCokernel
import Wikipedia.HopfProblem.SheafHigherDirectImageExtBasic

/-!
# Literal degree-two cycle classes in the original three-term window

The native comparison with the consecutive terms in degrees one, two, and
three preserves each actual degree-two cocycle representative. Its short
complex isomorphism has the identity as its middle component; no sign or
replacement cycle class is introduced.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ExponentialChernComparison.GlobalCycle

open ConstantSheafSingularComparison.LowExt.CycleCokernel
open SheafHigherDirectImage

/-- A cocycle for the literal degree-two differential is closed for the
native short complex, whose next index is chosen by the complex shape. -/
theorem closed_sc (K : CochainComplex AddCommGrpCat.{0} ℕ) (ζ : K.X 2)
    (hζ : K.d 2 3 ζ = 0) : (K.sc 2).g ζ = 0 := by
  change K.d 2 ((ComplexShape.up ℕ).next 2) ζ = 0
  rw [CochainComplex.next]
  exact hζ

/-- The actual window comparison sends the original degree-two cycle
class to the class of the identical representative in its three-term window. -/
@[simp] theorem windowHomologyIso₂_hom_cycleClass
    (K : CochainComplex AddCommGrpCat.{0} ℕ) (ζ : K.X 2) (hζ : K.d 2 3 ζ = 0) :
    (windowHomologyIso₂ K).hom (ExtBridge.cycleClass K 2 ζ (closed_sc K ζ hζ)) =
      ExtBridge.shortCycleClass (K.sc' 1 2 3) ζ hζ := by
  let e : K.sc 2 ≅ K.sc' 1 2 3 :=
    K.isoSc' 1 2 3 ((ComplexShape.up ℕ).prev_eq' (by rfl))
      ((ComplexShape.up ℕ).next_eq' (by rfl))
  change ShortComplex.homologyMap e.hom
    (ExtBridge.shortCycleClass (K.sc 2) ζ (closed_sc K ζ hζ)) = _
  exact ExtBridge.shortHomologyMap_cycleClass e.hom ζ (closed_sc K ζ hζ) hζ

/-- The inverse comparison also preserves the original cocycle representative. -/
@[simp] theorem windowHomologyIso₂_inv_shortCycleClass
    (K : CochainComplex AddCommGrpCat.{0} ℕ) (ζ : K.X 2) (hζ : K.d 2 3 ζ = 0) :
    (windowHomologyIso₂ K).inv (ExtBridge.shortCycleClass (K.sc' 1 2 3) ζ hζ) =
      ExtBridge.cycleClass K 2 ζ (closed_sc K ζ hζ) := by
  calc
    _ = (windowHomologyIso₂ K).inv
        ((windowHomologyIso₂ K).hom
          (ExtBridge.cycleClass K 2 ζ (closed_sc K ζ hζ))) :=
      congrArg (windowHomologyIso₂ K).inv
        (windowHomologyIso₂_hom_cycleClass K ζ hζ).symm
    _ = _ := (windowHomologyIso₂ K).addCommGroupIsoToAddEquiv.symm_apply_apply _

end Wikipedia.HopfProblem.ExponentialChernComparison.GlobalCycle
