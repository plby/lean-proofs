import Wikipedia.HopfProblem.ThreefoldHomotopyThree
import Wikipedia.HopfProblem.FourthHurewicz

/-!
# The actual fourth homotopy group of the constructed threefold is trivial

The proved native connectivity through degree three makes the genuine fourth
Hurewicz map an isomorphism. Its target is the original fourth integral
singular homology, already proved zero from the full attachment maps.

This gives actual relative-boundary contractions of all based four-cubes,
without a sphere-recognition or homotopy-equivalence assumption.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomotopyFour

open SingularMayerVietoris

/-- The original native fourth Hurewicz map on the actual constructed space. -/
def hurewiczEquiv (x : Space) : Additive (π_ 4 Space x) ≃ₗ[ℤ] SingularHomology Space 4 := by
  letI := space_simplyConnected
  letI := HomotopyTwo.piTwo_subsingleton x
  letI := HomotopyThree.piThree_subsingleton x
  exact FourthHurewicz.hurewiczLinearEquiv x

@[simp] theorem hurewiczEquiv_toLinearMap (x : Space) :
    (hurewiczEquiv x).toLinearMap = FourthHurewicz.hurewiczMap x := rfl

/-- Its forward map is the original cube's actual singular homology class. -/
@[simp] theorem hurewiczEquiv_mk (x : Space) (p : GenLoop (Fin 4) Space x) :
    hurewiczEquiv x (Additive.ofMul (⟦p⟧ : π_ 4 Space x)) =
      FourthHurewicz.cubeHomologyClass p := rfl

/-- Native fourth homotopy is trivial at every original base point. -/
theorem piFour_subsingleton (x : Space) : Subsingleton (π_ 4 Space x) := by
  have := space_simplyConnected
  have := HomotopyTwo.piTwo_subsingleton x
  have := HomotopyThree.piThree_subsingleton x
  have := Homology.FourthDegree.homologyFour_subsingleton
  exact (FourthHurewicz.hurewiczPi4Equiv x).injective.subsingleton

theorem piFour_eq_one (x : Space) (a : π_ 4 Space x) : a = 1 :=
  (piFour_subsingleton x).elim _ _

theorem additive_piFour_eq_zero (x : Space) (a : Additive (π_ 4 Space x)) : a = 0 := by
  have := piFour_subsingleton x
  exact Subsingleton.elim _ _

/-- Every actual based four-cube contracts while its full boundary stays fixed. -/
theorem genLoop_four_nullhomotopic (x : Space) (p : GenLoop (Fin 4) Space x) :
    GenLoop.Homotopic p GenLoop.const :=
  Quotient.exact (@Subsingleton.elim (π_ 4 Space x)
    (piFour_subsingleton x) ⟦p⟧ ⟦GenLoop.const⟧)

/-- The first four genuine connectivity conditions hold in the original topology. -/
theorem space_four_connected :
    SimplyConnectedSpace Space ∧
      (∀ x : Space, Subsingleton (π_ 2 Space x)) ∧
      (∀ x : Space, Subsingleton (π_ 3 Space x)) ∧
      ∀ x : Space, Subsingleton (π_ 4 Space x) :=
  ⟨space_simplyConnected, HomotopyTwo.piTwo_subsingleton,
    HomotopyThree.piThree_subsingleton, piFour_subsingleton⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomotopyFour
