import Wikipedia.HopfProblem.SheafCupProductScalarQuotientBasic

/-!
# The actual scalar maps on coface quotient groups

The scalar maps descend literal multiplication on cocycles through the
actual boundary subgroups. The product laws follow from the original
Alexander–Whitney representatives, with no transported quotient module.
-/

namespace Wikipedia.HopfProblem.SheafCupProduct.ScalarQuotient.CompatibleCoefficients

universe u v

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  {K : Type v} [CommRing K] {D : Coface.Data R0 R1 R2 R3}
  (c : CompatibleCoefficients K D)

/-- Literal scalar multiplication descended to the actual first quotient. -/
def scalarOne (z : K) : D.CohomologyOne →+ D.CohomologyOne :=
  QuotientAddGroup.lift D.boundariesOne (D.classOne.comp (c.cocycleScalarOne z)) (by
    intro a ha
    obtain ⟨r, rfl⟩ := ha
    change D.classOne (c.cocycleScalarOne z (D.boundaryOne r)) = 0
    rw [c.cocycleScalarOne_boundary, D.classOne_boundary])

/-- Literal scalar multiplication descended to the actual second quotient. -/
def scalarTwo (z : K) : D.CohomologyTwo →+ D.CohomologyTwo :=
  QuotientAddGroup.lift D.boundariesTwo (D.classTwo.comp (c.cocycleScalarTwo z)) (by
    intro a ha
    obtain ⟨b, rfl⟩ := ha
    change D.classTwo (c.cocycleScalarTwo z (D.boundaryTwo b)) = 0
    rw [c.cocycleScalarTwo_boundary, D.classTwo_boundary])

@[simp] theorem scalarOne_class (z : K) (a : D.CocycleOne) :
    c.scalarOne z (D.classOne a) = D.classOne (c.cocycleScalarOne z a) := rfl

@[simp] theorem scalarTwo_class (z : K) (a : D.CocycleTwo) :
    c.scalarTwo z (D.classTwo a) = D.classTwo (c.cocycleScalarTwo z a) := rfl

/-- The literal Alexander–Whitney cocycle is linear in the first input. -/
theorem cupCocycle_scalar_left (z : K) (a b : D.CocycleOne) :
    D.cupCocycle (c.cocycleScalarOne z a) b = c.cocycleScalarTwo z (D.cupCocycle a b) := by
  apply Subtype.ext
  change D.δ1 2 (c.c1 z * (a : R1)) * D.δ1 0 (b : R1) =
    c.c2 z * (D.δ1 2 (a : R1) * D.δ1 0 (b : R1))
  rw [map_mul, c.face1, mul_assoc]

/-- The literal Alexander–Whitney cocycle is linear in the second input. -/
theorem cupCocycle_scalar_right (z : K) (a b : D.CocycleOne) :
    D.cupCocycle a (c.cocycleScalarOne z b) = c.cocycleScalarTwo z (D.cupCocycle a b) := by
  apply Subtype.ext
  change D.δ1 2 (a : R1) * D.δ1 0 (c.c1 z * (b : R1)) =
    c.c2 z * (D.δ1 2 (a : R1) * D.δ1 0 (b : R1))
  rw [map_mul, c.face1, mul_left_comm]

/-- The quotient Alexander–Whitney product is scalar-linear in the first input. -/
theorem cup_scalar_left (z : K) (a b : D.CohomologyOne) :
    D.cup (c.scalarOne z a) b = c.scalarTwo z (D.cup a b) := by
  obtain ⟨a, rfl⟩ := D.classOne_surjective a
  obtain ⟨b, rfl⟩ := D.classOne_surjective b
  rw [c.scalarOne_class, D.cup_classOne, D.cup_classOne, c.scalarTwo_class,
    c.cupCocycle_scalar_left]

/-- The quotient Alexander–Whitney product is scalar-linear in the second input. -/
theorem cup_scalar_right (z : K) (a b : D.CohomologyOne) :
    D.cup a (c.scalarOne z b) = c.scalarTwo z (D.cup a b) := by
  obtain ⟨a, rfl⟩ := D.classOne_surjective a
  obtain ⟨b, rfl⟩ := D.classOne_surjective b
  rw [c.scalarOne_class, D.cup_classOne, D.cup_classOne, c.scalarTwo_class,
    c.cupCocycle_scalar_right]

end Wikipedia.HopfProblem.SheafCupProduct.ScalarQuotient.CompatibleCoefficients
