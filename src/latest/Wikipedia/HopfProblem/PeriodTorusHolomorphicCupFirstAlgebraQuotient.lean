import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstAlgebraCocycles
import Wikipedia.HopfProblem.SheafCupProductCofaceQuotient

/-!
# The canonical first-column maps on the original cohomology quotients

True boundary descent defines the quotient maps. Their cup compatibility
is proved on the literal cocycle representatives of the existing products.
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstAlgebra.Data

variable {A0 A1 A2 A3 R0 R1 R2 R3 : Type u}
  [CommRing A0] [CommRing A1] [CommRing A2] [CommRing A3]
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  {E : SheafCupProduct.Coface.Data A0 A1 A2 A3}
  {D : Algebra.Data R0 R1 R2 R3} (F : Data E D)

/-- The induced map on the original first kernel/range quotient. -/
def cohomologyOneMap : E.CohomologyOne →+ D.CohomologyOne :=
  QuotientAddGroup.lift E.boundariesOne (D.classOne.comp F.cocycleOneMap) (by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    change D.classOne (F.cocycleOneMap (E.boundaryOne u)) = 0
    rw [F.cocycleOneMap_boundary, D.classOne_boundary])

/-- The induced map on the original second kernel/range quotient. -/
def cohomologyTwoMap : E.CohomologyTwo →+ D.CohomologyTwo :=
  QuotientAddGroup.lift E.boundariesTwo (D.classTwo.comp F.cocycleTwoMap) (by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    change D.classTwo (F.cocycleTwoMap (E.boundaryTwo u)) = 0
    rw [F.cocycleTwoMap_boundary, D.classTwo_boundary])

@[simp] theorem cohomologyOneMap_classOne (x : E.CocycleOne) :
    F.cohomologyOneMap (E.classOne x) = D.classOne (F.cocycleOneMap x) := rfl

@[simp] theorem cohomologyTwoMap_classTwo (x : E.CocycleTwo) :
    F.cohomologyTwoMap (E.classTwo x) = D.classTwo (F.cocycleTwoMap x) := rfl

/-- The first quotient map retains the literal first-column representative. -/
theorem cohomologyOneMap_representative (x : A1) (hx : E.d1 x = 0) :
    F.cohomologyOneMap (E.classOne ⟨x, hx⟩) =
      D.classOne ⟨(F.morphism.f1 x, 0), F.mapOne_isCocycle hx⟩ := rfl

/-- The second quotient map retains the literal first-column representative. -/
theorem cohomologyTwoMap_representative (x : A2) (hx : E.d2 x = 0) :
    F.cohomologyTwoMap (E.classTwo ⟨x, hx⟩) =
      D.classTwo ⟨(F.morphism.f2 x, 0, 0), F.mapTwo_isCocycle hx⟩ := rfl

/-- The canonical first-column quotient maps preserve the existing cup products. -/
theorem map_cup (x y : E.CohomologyOne) :
    F.cohomologyTwoMap (E.cup x y) =
      D.cup (F.cohomologyOneMap x) (F.cohomologyOneMap y) := by
  obtain ⟨x, rfl⟩ := E.classOne_surjective x
  obtain ⟨y, rfl⟩ := E.classOne_surjective y
  rw [E.cup_classOne, F.cohomologyTwoMap_classTwo, F.cohomologyOneMap_classOne,
    F.cohomologyOneMap_classOne, D.cup_classOne, F.cocycleTwoMap_cup]

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstAlgebra.Data
