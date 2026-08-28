import Wikipedia.HopfProblem.SheafCupProductCofaceQuotient

/-!
# Scalar multiplication on the actual coface cocycles

The four coefficient maps are preserved by every coface. Literal
multiplication therefore commutes with each alternating differential,
preserves its actual kernel, and sends actual boundaries to boundaries.
-/

namespace Wikipedia.HopfProblem.SheafCupProduct.ScalarQuotient

universe u v

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]

/-- Four actual coefficient homomorphisms preserved by all the original cofaces. -/
structure CompatibleCoefficients (K : Type v) [CommRing K]
    (D : Coface.Data R0 R1 R2 R3) where
  c0 : K →+* R0
  c1 : K →+* R1
  c2 : K →+* R2
  c3 : K →+* R3
  face0 : ∀ i z, D.δ0 i (c0 z) = c1 z
  face1 : ∀ i z, D.δ1 i (c1 z) = c2 z
  face2 : ∀ i z, D.δ2 i (c2 z) = c3 z

namespace CompatibleCoefficients

variable {K : Type v} [CommRing K] {D : Coface.Data R0 R1 R2 R3}
  (c : CompatibleCoefficients K D)

theorem d0_mul (z : K) (r : R0) : D.d0 (c.c0 z * r) = c.c1 z * D.d0 r := by
  simp only [Coface.Data.d0_apply, map_mul, c.face0, mul_sub]

theorem d1_mul (z : K) (a : R1) : D.d1 (c.c1 z * a) = c.c2 z * D.d1 a := by
  simp only [Coface.Data.d1_apply, map_mul, c.face1, mul_sub, mul_add]

theorem d2_mul (z : K) (a : R2) : D.d2 (c.c2 z * a) = c.c3 z * D.d2 a := by
  simp only [Coface.Data.d2_apply, map_mul, c.face2, mul_sub, mul_add]

/-- Multiplication by the original coefficient preserves first cocycles. -/
def cocycleScalarOne (z : K) : D.CocycleOne →+ D.CocycleOne where
  toFun a := ⟨c.c1 z * (a : R1), by
    change D.d1 (c.c1 z * (a : R1)) = 0
    rw [c.d1_mul, a.property, mul_zero]⟩
  map_zero' := Subtype.ext (mul_zero (c.c1 z))
  map_add' a b := Subtype.ext (mul_add (c.c1 z) (a : R1) (b : R1))

/-- Multiplication by the original coefficient preserves second cocycles. -/
def cocycleScalarTwo (z : K) : D.CocycleTwo →+ D.CocycleTwo where
  toFun a := ⟨c.c2 z * (a : R2), by
    change D.d2 (c.c2 z * (a : R2)) = 0
    rw [c.d2_mul, a.property, mul_zero]⟩
  map_zero' := Subtype.ext (mul_zero (c.c2 z))
  map_add' a b := Subtype.ext (mul_add (c.c2 z) (a : R2) (b : R2))

@[simp] theorem cocycleScalarOne_coe (z : K) (a : D.CocycleOne) :
    (c.cocycleScalarOne z a : R1) = c.c1 z * (a : R1) := rfl

@[simp] theorem cocycleScalarTwo_coe (z : K) (a : D.CocycleTwo) :
    (c.cocycleScalarTwo z a : R2) = c.c2 z * (a : R2) := rfl

/-- The image of a first boundary is the boundary of the literal scalar multiple. -/
theorem cocycleScalarOne_boundary (z : K) (r : R0) :
    c.cocycleScalarOne z (D.boundaryOne r) = D.boundaryOne (c.c0 z * r) :=
  Subtype.ext (c.d0_mul z r).symm

/-- The image of a second boundary is the boundary of the literal scalar multiple. -/
theorem cocycleScalarTwo_boundary (z : K) (a : R1) :
    c.cocycleScalarTwo z (D.boundaryTwo a) = D.boundaryTwo (c.c1 z * a) :=
  Subtype.ext (c.d1_mul z a).symm

end CompatibleCoefficients

end Wikipedia.HopfProblem.SheafCupProduct.ScalarQuotient
