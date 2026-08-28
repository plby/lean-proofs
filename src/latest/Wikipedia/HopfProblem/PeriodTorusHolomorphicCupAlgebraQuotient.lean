import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebraCocycles

/-!
# The genuine kernel/range quotient cup of the Dolbeault total algebra

The proved two-sided boundary primitives make the literal cochain
product descend in each variable. Its cohomology-class formula is the
original signed vertical, mixed, and horizontal product.
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  (D : Data R0 R1 R2 R3)

def cupRight (x : D.CocycleOne) : D.CohomologyOne →+ D.CohomologyTwo :=
  QuotientAddGroup.lift D.boundariesOne (D.classTwo.comp (D.cupCocycles x)) (by
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    change D.classTwo (D.cupCocycles x (D.boundaryOne u)) = 0
    rw [D.cupCocycles_boundary_right, D.classTwo_boundary])

@[simp] theorem cupRight_classOne (x y : D.CocycleOne) :
    D.cupRight x (D.classOne y) = D.classTwo (D.cupCocycles x y) := rfl

def cupRightHom : D.CocycleOne →+ D.CohomologyOne →+ D.CohomologyTwo where
  toFun := D.cupRight
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    obtain ⟨y, rfl⟩ := D.classOne_surjective y
    simp only [cupRight_classOne, map_zero, AddMonoidHom.zero_apply]
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    obtain ⟨z, rfl⟩ := D.classOne_surjective z
    simp only [AddMonoidHom.add_apply, cupRight_classOne, map_add]

theorem cupRightHom_boundary (u : R0) : D.cupRightHom (D.boundaryOne u) = 0 := by
  apply AddMonoidHom.ext
  intro y
  obtain ⟨y, rfl⟩ := D.classOne_surjective y
  change D.classTwo (D.cupCocycles (D.boundaryOne u) y) = 0
  rw [D.cupCocycles_boundary_left, D.classTwo_boundary]

/-- The actual biadditive product on the actual kernel/range quotient groups. -/
def cup : D.CohomologyOne →+ D.CohomologyOne →+ D.CohomologyTwo :=
  QuotientAddGroup.lift D.boundariesOne D.cupRightHom (by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact D.cupRightHom_boundary u)

@[simp] theorem cup_classOne (x y : D.CocycleOne) :
    D.cup (D.classOne x) (D.classOne y) = D.classTwo (D.cupCocycle x y) := rfl

/-- Every quotient product retains the requested literal signed representative. -/
theorem cup_representatives (x y : D.One) (hx : D.d1 x = 0) (hy : D.d1 y = 0) :
    D.cup (D.classOne ⟨x, hx⟩) (D.classOne ⟨y, hy⟩) =
      D.classTwo ⟨(D.cofaces.δ1 2 x.1 * D.cofaces.δ1 0 y.1,
        (x.1 * D.cofaces.δ0 0 y.2.1 - D.cofaces.δ0 1 x.2.1 * y.1,
          x.1 * D.cofaces.δ0 0 y.2.2 - D.cofaces.δ0 1 x.2.2 * y.1),
        x.2.1 * y.2.2 - x.2.2 * y.2.1), D.cupOne_isCocycle hx hy⟩ := rfl

theorem cup_add_left (x y z : D.CohomologyOne) :
    D.cup (x + y) z = D.cup x z + D.cup y z := by
  rw [map_add, AddMonoidHom.add_apply]

theorem cup_add_right (x y z : D.CohomologyOne) :
    D.cup x (y + z) = D.cup x y + D.cup x z := map_add (D.cup x) y z

theorem cup_unique (μ : D.CohomologyOne →+ D.CohomologyOne →+ D.CohomologyTwo)
    (hμ : ∀ x y : D.CocycleOne, μ (D.classOne x) (D.classOne y) =
      D.classTwo (D.cupCocycle x y)) : μ = D.cup := by
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := D.classOne_surjective x
  obtain ⟨y, rfl⟩ := D.classOne_surjective y
  exact hμ x y

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data
