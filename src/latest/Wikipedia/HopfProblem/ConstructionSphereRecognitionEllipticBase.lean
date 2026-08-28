import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticAction
import Wikipedia.HopfProblem.EllipticQuotientFibration
import Wikipedia.HopfProblem.EllipticDiscPower

/-!
# The original power projection on the native finite cap quotient

The map is descended from `s ↦ s^m` on the actual disc-fibre cover.
Its definition is independent of the product coordinates used later.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticModel

open SpecialPeriods ThreefoldOverlapMappingTorus
open Wikipedia.HopfProblem.Elliptic

variable (m : ℕ) [NeZero m]

theorem discPower_rotate (c : Circle) (s : Disc) :
    discPower m (Nat.pos_of_ne_zero (NeZero.ne m)) (rotate c s) =
      rotate (m • c) (discPower m (Nat.pos_of_ne_zero (NeZero.ne m)) s) :=
  Subtype.ext (rotate_pow c s m)

variable {X : Type*} [TopologicalSpace X] (B : X ≃ₜ X) (hB : B ^ m = 1)

theorem capBase_invariant (g : Multiplicative (ZMod m)) (p : Disc × X) :
    letI := capAction m B hB
    discPower m (Nat.pos_of_ne_zero (NeZero.ne m)) (g • p).1 =
      discPower m (Nat.pos_of_ne_zero (NeZero.ne m)) p.1 := by
  change discPower m _ (((capPermutation m B ^ g.toAdd.val) p).1) = _
  rw [capPermutation_pow_apply, discPower_rotate, smul_comm m g.toAdd.val,
    smul_neg, order_smul_sector, neg_zero, smul_zero, rotate_zero]

/-- The actual quotient descent of the original power projection. -/
def capBase : C(CapQuotient m B hB, Disc) := by
  let := capAction m B hB
  exact ⟨FiniteQuotient.descend
    (fun p : Disc × X => discPower m (Nat.pos_of_ne_zero (NeZero.ne m)) p.1)
    (capBase_invariant m B hB),
    FiniteQuotient.descend_continuous _ _
      ((discPower_continuous m (Nat.pos_of_ne_zero (NeZero.ne m))).comp continuous_fst)⟩

@[simp] theorem capBase_project (p : Disc × X) :
    capBase m B hB (capProject m B hB p) =
      discPower m (Nat.pos_of_ne_zero (NeZero.ne m)) p.1 := rfl

@[simp] theorem capBase_project_val (p : Disc × X) :
    (capBase m B hB (capProject m B hB p) : ℂ) = (p.1 : ℂ) ^ m := rfl

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticModel
