import Wikipedia.HopfProblem.ThreefoldHomotopyFour
import Wikipedia.HopfProblem.FifthHurewicz

/-!
# The actual fifth homotopy group of the constructed threefold is trivial

The original fifth Hurewicz map is an isomorphism because the constructed
space is simply connected and its native second, third, and fourth homotopy
groups vanish. Its target is the original fifth integral singular homology,
already proved zero using the actual attachment maps.

In particular, every genuine based five-cube contracts relative to its full
boundary. No sphere-recognition hypothesis or homotopy equivalence is used.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomotopyFive

open SingularMayerVietoris

/-- The original native fifth Hurewicz map on the constructed space. -/
def hurewiczEquiv (x : Space) : Additive (π_ 5 Space x) ≃ₗ[ℤ] SingularHomology Space 5 := by
  letI := space_simplyConnected
  letI := HomotopyTwo.piTwo_subsingleton x
  letI := HomotopyThree.piThree_subsingleton x
  letI := HomotopyFour.piFour_subsingleton x
  exact FifthHurewicz.hurewiczLinearEquiv x

@[simp] theorem hurewiczEquiv_toLinearMap (x : Space) :
    (hurewiczEquiv x).toLinearMap = FifthHurewicz.hurewiczMap x := rfl

/-- The forward map retains the original five-cube's singular homology class. -/
@[simp] theorem hurewiczEquiv_mk (x : Space) (p : GenLoop (Fin 5) Space x) :
    hurewiczEquiv x (Additive.ofMul (⟦p⟧ : π_ 5 Space x)) =
      FifthHurewicz.cubeHomologyClass p := rfl

/-- Native fifth homotopy is trivial at every original base point. -/
theorem piFive_subsingleton (x : Space) : Subsingleton (π_ 5 Space x) := by
  have := space_simplyConnected
  have := HomotopyTwo.piTwo_subsingleton x
  have := HomotopyThree.piThree_subsingleton x
  have := HomotopyFour.piFour_subsingleton x
  have := Homology.FifthDegree.homologyFive_subsingleton
  exact (FifthHurewicz.hurewiczPi5Equiv x).injective.subsingleton

theorem piFive_eq_one (x : Space) (a : π_ 5 Space x) : a = 1 :=
  (piFive_subsingleton x).elim _ _

theorem additive_piFive_eq_zero (x : Space) (a : Additive (π_ 5 Space x)) : a = 0 := by
  have := piFive_subsingleton x
  exact Subsingleton.elim _ _

/-- Every original based five-cube contracts while its full boundary remains fixed. -/
theorem genLoop_five_nullhomotopic (x : Space) (p : GenLoop (Fin 5) Space x) :
    GenLoop.Homotopic p GenLoop.const :=
  Quotient.exact (@Subsingleton.elim (π_ 5 Space x)
    (piFive_subsingleton x) ⟦p⟧ ⟦GenLoop.const⟧)

/-- The first five native connectivity conditions hold in the original topology. -/
theorem space_five_connected :
    SimplyConnectedSpace Space ∧
      (∀ x : Space, Subsingleton (π_ 2 Space x)) ∧
      (∀ x : Space, Subsingleton (π_ 3 Space x)) ∧
      (∀ x : Space, Subsingleton (π_ 4 Space x)) ∧
      ∀ x : Space, Subsingleton (π_ 5 Space x) :=
  ⟨space_simplyConnected, HomotopyTwo.piTwo_subsingleton,
    HomotopyThree.piThree_subsingleton, HomotopyFour.piFour_subsingleton,
    piFive_subsingleton⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomotopyFive
