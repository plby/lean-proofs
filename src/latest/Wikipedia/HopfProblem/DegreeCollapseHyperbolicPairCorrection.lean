import Wikipedia.NoExoticSixSphere.ArfPlanes
import Mathlib.LinearAlgebra.Prod

/-!
# Correct a geometric unit pair to a hyperbolic pair and retain its projection

For a quadratic zero vector a with B(a,b)=1, replace b by b+q(b)a.
Both vectors then have quadratic value zero. Projection along the second
vector maps the original space onto the actual kernel of B(a,-), with
explicit linear and quadratic formulas. No nondegeneracy or dimension
hypothesis is used.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.HyperbolicReduction

open NoExoticSixSphere.Arf

variable {V : Type*} [AddCommGroup V] [Module F₂ V]
  (q : QuadraticForm F₂ V) (B : V →ₗ[F₂] V →ₗ[F₂] F₂) (hB : q.polarBilin = B)

include hB in
theorem symmetric (x y : V) : B x y = B y x := by
  rw [← hB]
  exact QuadraticMap.polar_comm q x y

include hB in
theorem self_zero (x : V) (hx : q x = 0) : B x x = 0 := by
  rw [← hB]
  change QuadraticMap.polar q x x = 0
  rw [QuadraticMap.polar_self, hx, nsmul_zero]

def correctedRight (a b : V) : V := b + q b • a

include hB in
theorem correctedRight_cross (a b : V) (ha : q a = 0) (hab : B a b = 1) :
    B a (correctedRight q a b) = 1 := by
  rw [correctedRight, map_add, map_smul, self_zero q B hB a ha, smul_zero, add_zero, hab]

include hB in
theorem correctedRight_zero (a b : V) (ha : q a = 0) (hab : B a b = 1) :
    q (correctedRight q a b) = 0 := by
  have hba : B b a = 1 := (symmetric q B hB b a).trans hab
  rw [correctedRight, QuadraticMap.map_add q, q.map_smul, ha, smul_zero, add_zero]
  change q b + q.polarBilin b (q b • a) = 0
  rw [hB]
  rw [map_smul, hba, smul_eq_mul, mul_one, ← two_mul]
  rw [show (2 : F₂) = 0 from by decide, zero_mul]

variable (a b : V) (ha : q a = 0) (hb : q b = 0) (hab : B a b = 1)

def leftInKernel : LinearMap.ker (B a) := ⟨a, self_zero q B hB a ha⟩

def projection : V →ₗ[F₂] LinearMap.ker (B a) :=
  (LinearMap.id - (B a).smulRight b).codRestrict _ (fun x ↦ by
    change B a (x - B a x • b) = 0
    rw [map_sub, map_smul, hab, smul_eq_mul, mul_one, sub_self])

theorem projection_val (x : V) : (projection B a b hab x).val = x - B a x • b := rfl

theorem projection_fixed (x : LinearMap.ker (B a)) : projection B a b hab x.val = x := by
  apply Subtype.ext
  rw [projection_val, show B a x.val = 0 from x.property, zero_smul, sub_zero]

theorem projection_right : projection B a b hab b = 0 := by
  apply Subtype.ext
  rw [projection_val, hab, one_smul, sub_self]
  rfl

include hB hb in
theorem right_coordinate_projection (x : V) : B b (projection B a b hab x).val = B b x := by
  rw [projection_val, map_sub, map_smul, self_zero q B hB b hb, smul_zero, sub_zero]

include hB hb in
theorem projection_quadratic (x : V) :
    q (projection B a b hab x).val = q x - B a x * B b x := by
  rw [projection_val, sub_eq_add_neg, QuadraticMap.map_add q, q.map_neg,
    q.map_smul, hb, smul_zero, add_zero]
  change q x + q.polarBilin x (-(B a x • b)) = q x - B a x * B b x
  rw [hB]
  rw [map_neg, map_smul, symmetric q B hB x b, smul_eq_mul, sub_eq_add_neg]

end Wikipedia.HopfProblem.DegreeCollapse.HyperbolicReduction
