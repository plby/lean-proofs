import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalAlgebraCocycles

/-!
# The actual total cup product on kernel/range quotient cohomology

The two explicit total boundary primitives make the pairing descend in
both variables. The resulting biadditive product retains its literal
Alexander--Whitney representative formula. No Eilenberg--Zilber theorem
or comparison with sheaf or singular cohomology is assumed here.
-/

universe u

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [CommRing R00] [CommRing R10] [CommRing R01] [CommRing R20] [CommRing R11]
  [CommRing R02] [CommRing R30] [CommRing R21] [CommRing R12] [CommRing R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

def cupRight (a : D.CocycleOne) : D.CohomologyOne →+ D.CohomologyTwo :=
  QuotientAddGroup.lift D.boundariesOne (D.classTwo.comp (D.cupCocycles a)) (by
    intro b hb
    obtain ⟨r, rfl⟩ := hb
    change D.classTwo (D.cupCocycles a (D.boundaryOne r)) = 0
    rw [D.cupCocycles_boundary_right, D.classTwo_boundary])

@[simp] theorem cupRight_classOne (a b : D.CocycleOne) :
    D.cupRight a (D.classOne b) = D.classTwo (D.cupCocycles a b) := rfl

def cupRightHom : D.CocycleOne →+ D.CohomologyOne →+ D.CohomologyTwo where
  toFun := D.cupRight
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    obtain ⟨b, rfl⟩ := D.classOne_surjective b
    simp only [cupRight_classOne, map_zero, AddMonoidHom.zero_apply]
  map_add' a b := by
    apply AddMonoidHom.ext
    intro c
    obtain ⟨c, rfl⟩ := D.classOne_surjective c
    simp only [AddMonoidHom.add_apply, cupRight_classOne, map_add]

theorem cupRightHom_boundary (r : R00) : D.cupRightHom (D.boundaryOne r) = 0 := by
  apply AddMonoidHom.ext
  intro b
  obtain ⟨b, rfl⟩ := D.classOne_surjective b
  change D.classTwo (D.cupCocycles (D.boundaryOne r) b) = 0
  rw [D.cupCocycles_boundary_left, D.classTwo_boundary]

/-- The biadditive actual total cup product on the genuine kernel/range quotients. -/
def cup : D.CohomologyOne →+ D.CohomologyOne →+ D.CohomologyTwo :=
  QuotientAddGroup.lift D.boundariesOne D.cupRightHom (by
    intro a ha
    obtain ⟨r, rfl⟩ := ha
    exact D.cupRightHom_boundary r)

@[simp] theorem cup_classOne (a b : D.CocycleOne) :
    D.cup (D.classOne a) (D.classOne b) = D.classTwo (D.cupCocycle a b) := rfl

/-- The quotient product is represented by the specified literal three-component formula. -/
theorem cup_representatives (a b : D.One) (ha : D.d1 a = 0) (hb : D.d1 b = 0) :
    D.cup (D.classOne ⟨a, ha⟩) (D.classOne ⟨b, hb⟩) =
      D.classTwo ⟨(D.v10 2 a.1 * D.v10 0 b.1,
        D.h10 1 a.1 * D.v01 0 b.2 - D.v01 1 a.2 * D.h10 0 b.1,
        D.h01 2 a.2 * D.h01 0 b.2), D.cupOne_isCocycle ha hb⟩ := rfl

theorem cup_add_left (a b c : D.CohomologyOne) :
    D.cup (a + b) c = D.cup a c + D.cup b c := by
  rw [map_add, AddMonoidHom.add_apply]

theorem cup_add_right (a b c : D.CohomologyOne) :
    D.cup a (b + c) = D.cup a b + D.cup a c := map_add (D.cup a) b c

theorem cup_unique (μ : D.CohomologyOne →+ D.CohomologyOne →+ D.CohomologyTwo)
    (hμ : ∀ a b : D.CocycleOne, μ (D.classOne a) (D.classOne b) =
      D.classTwo (D.cupCocycle a b)) : μ = D.cup := by
  apply AddMonoidHom.ext
  intro a
  apply AddMonoidHom.ext
  intro b
  obtain ⟨a, rfl⟩ := D.classOne_surjective a
  obtain ⟨b, rfl⟩ := D.classOne_surjective b
  exact hμ a b

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data
