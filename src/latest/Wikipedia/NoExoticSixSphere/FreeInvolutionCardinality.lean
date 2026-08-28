import Wikipedia.NoExoticSixSphere.InvolutionQuotient
import Mathlib.Data.Finite.Card
import Mathlib.Logic.Equiv.Sum

/-!
# Two actual sheets over each free involution orbit

Every fiber of the genuine orbit projection has two elements. Choosing an
actual representative in each orbit gives an equivalence with the orbit
set times `Bool`, and hence the exact finite cardinality relation.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.InvolutionQuotient

variable {X : Type*} (σ : X → X) (hσ : Involutive σ) (hfree : ∀ x, σ x ≠ x)

def boolFiberEquiv (x : X) : Bool ≃ {y // proj σ hσ y = proj σ hσ x} := by
  classical
  exact {
    toFun b := cond b ⟨σ x, proj_swap σ hσ x⟩ ⟨x, rfl⟩
    invFun y := decide (y.val ≠ x)
    left_inv b := by cases b <;> simp [hfree x]
    right_inv y := by
      apply Subtype.ext
      rcases (proj_eq_iff σ hσ y.val x).mp y.property with hy | hy
      · simp [hy]
      · have he : y.val = σ x := (hσ y.val).symm.trans (congrArg σ hy)
        simp [he, hfree x] }

def fiberEquivBool (q : Orbit σ hσ) : {y // proj σ hσ y = q} ≃ Bool := by
  let x := Quotient.out q
  have hx : proj σ hσ x = q := Quotient.out_eq q
  exact (Equiv.setCongr (congrArg (fun v ↦ {y | proj σ hσ y = v}) hx.symm)).trans
    (boolFiberEquiv σ hσ hfree x).symm

def twoSheetEquiv : X ≃ Orbit σ hσ × Bool :=
  (Equiv.sigmaFiberEquiv (proj σ hσ)).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fiberEquivBool σ hσ hfree))

include hfree in
theorem card_eq_twice_orbits [Finite X] : Nat.card X = 2 * Nat.card (Orbit σ hσ) := by
  rw [Nat.card_congr (twoSheetEquiv σ hσ hfree), Nat.card_prod]
  simp [Nat.mul_comm]

end NoExoticSixSphere.InvolutionQuotient
