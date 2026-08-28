import Wikipedia.HopfProblem.SheafCupProductCofaceQuotient

/-!
# Explicit degree-one skew commutativity

For closed degree-one cochains, the symmetric sum of the two
Alexander–Whitney products is the differential of the literal cochain
`-(a*b)`. Hence the quotient pairing is skew-commutative.
-/

universe u₀ u₁ u₂ u₃

namespace Wikipedia.HopfProblem.SheafCupProduct.Coface.Data

variable {R0 : Type u₀} {R1 : Type u₁} {R2 : Type u₂} {R3 : Type u₃}
variable [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
variable (D : Coface.Data R0 R1 R2 R3)

theorem middle_coface_of_cocycle {a : R1} (ha : D.d1 a = 0) :
    D.δ1 1 a = D.δ1 0 a + D.δ1 2 a := by
  calc
    D.δ1 1 a = D.δ1 0 a + D.δ1 2 a - D.d1 a := by rw [d1_apply]; ring
    _ = D.δ1 0 a + D.δ1 2 a := by rw [ha, sub_zero]

theorem cupOne_add_swap {a b : R1} (ha : D.d1 a = 0) (hb : D.d1 b = 0) :
    D.cupOne a b + D.cupOne b a = D.d1 (-(a * b)) := by
  simp only [cupOne, d1_apply, map_neg, map_mul]
  rw [D.middle_coface_of_cocycle ha, D.middle_coface_of_cocycle hb]
  ring

theorem cupCocycle_add_swap (a b : D.CocycleOne) :
    D.cupCocycle a b + D.cupCocycle b a = D.boundaryTwo (-((a : R1) * (b : R1))) :=
  Subtype.ext (D.cupOne_add_swap a.property b.property)

theorem cup_add_swap (a b : D.CohomologyOne) : D.cup a b + D.cup b a = 0 := by
  obtain ⟨a, rfl⟩ := D.classOne_surjective a
  obtain ⟨b, rfl⟩ := D.classOne_surjective b
  rw [D.cup_classOne, D.cup_classOne, ← map_add, D.cupCocycle_add_swap, D.classTwo_boundary]

theorem cup_skew_comm (a b : D.CohomologyOne) : D.cup a b = -D.cup b a :=
  eq_neg_iff_add_eq_zero.mpr (D.cup_add_swap a b)

end Wikipedia.HopfProblem.SheafCupProduct.Coface.Data
