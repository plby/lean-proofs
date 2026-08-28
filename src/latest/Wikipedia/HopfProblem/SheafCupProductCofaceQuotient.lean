import Wikipedia.HopfProblem.SheafCupProductCofaceCocycles

/-!
# Alexander–Whitney pairing on the genuine kernel/range quotients

The explicit boundary primitives make the cocycle pairing vanish on
boundaries in either variable. Two quotient-group lifts therefore give
an additive pairing in both variables, with the literal representative
formula retained.
-/

universe u₀ u₁ u₂ u₃

namespace Wikipedia.HopfProblem.SheafCupProduct.Coface.Data

variable {R0 : Type u₀} {R1 : Type u₁} {R2 : Type u₂} {R3 : Type u₃}
variable [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
variable (D : Coface.Data R0 R1 R2 R3)

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

theorem cupRightHom_boundary (r : R0) : D.cupRightHom (D.boundaryOne r) = 0 := by
  apply AddMonoidHom.ext
  intro b
  obtain ⟨b, rfl⟩ := D.classOne_surjective b
  change D.classTwo (D.cupCocycles (D.boundaryOne r) b) = 0
  rw [D.cupCocycles_boundary_left, D.classTwo_boundary]

/-- The bilinear Alexander–Whitney product on the actual cohomology
quotients of the alternating coface differential. -/
def cup : D.CohomologyOne →+ D.CohomologyOne →+ D.CohomologyTwo :=
  QuotientAddGroup.lift D.boundariesOne D.cupRightHom (by
    intro a ha
    obtain ⟨r, rfl⟩ := ha
    exact D.cupRightHom_boundary r)

@[simp] theorem cup_classOne (a b : D.CocycleOne) :
    D.cup (D.classOne a) (D.classOne b) = D.classTwo (D.cupCocycle a b) := rfl

/-- The quotient product is represented by the literal ring-coface
formula, with its cocycle proof supplied by the proved identities. -/
theorem cup_representatives (a b : R1) (ha : D.d1 a = 0) (hb : D.d1 b = 0) :
    D.cup (D.classOne ⟨a, ha⟩) (D.classOne ⟨b, hb⟩) =
      D.classTwo ⟨D.δ1 2 a * D.δ1 0 b, D.cupOne_isCocycle ha hb⟩ := rfl

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

end Wikipedia.HopfProblem.SheafCupProduct.Coface.Data
