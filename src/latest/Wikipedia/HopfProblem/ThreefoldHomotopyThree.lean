import Wikipedia.HopfProblem.ThreefoldHomotopyTwo
import Wikipedia.HopfProblem.ThreefoldHomologyMiddleVanishing
import Wikipedia.HopfProblem.ThirdHurewicz

/-!
# The actual third homotopy group of the constructed threefold is trivial

The original simply connected topology, the proved native second-homotopy
vanishing and the genuine third Hurewicz isomorphism identify native third
homotopy with actual third integral homology. The latter now vanishes by the
original attachment relation. Every original based cube is therefore genuinely
nullhomotopic relative to its full boundary. No sphere recognition is used.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomotopyThree

open SingularMayerVietoris

/-- The genuine third Hurewicz map on the actual constructed space. -/
def hurewiczEquiv (x : Space) : Additive (π_ 3 Space x) ≃ₗ[ℤ] SingularHomology Space 3 := by
  letI := space_simplyConnected
  letI := HomotopyTwo.piTwo_subsingleton x
  exact ThirdHurewicz.hurewiczLinearEquiv x

@[simp] theorem hurewiczEquiv_toLinearMap (x : Space) :
    (hurewiczEquiv x).toLinearMap = ThirdHurewicz.hurewiczMap x := rfl

/-- Its forward map is the original native cube's actual singular homology class. -/
@[simp] theorem hurewiczEquiv_mk (x : Space) (p : GenLoop (Fin 3) Space x) :
    hurewiczEquiv x (Additive.ofMul (⟦p⟧ : π_ 3 Space x)) =
      ThirdHurewicz.cubeHomologyClass p := rfl

/-- Native third homotopy is trivial at every original base point. -/
theorem piThree_subsingleton (x : Space) : Subsingleton (π_ 3 Space x) := by
  have := space_simplyConnected
  have := HomotopyTwo.piTwo_subsingleton x
  have := Homology.ThirdDegree.homologyThree_subsingleton
  exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton

theorem piThree_eq_one (x : Space) (a : π_ 3 Space x) : a = 1 :=
  (piThree_subsingleton x).elim _ _

theorem additive_piThree_eq_zero (x : Space) (a : Additive (π_ 3 Space x)) : a = 0 := by
  have := piThree_subsingleton x
  exact Subsingleton.elim _ _

/-- Actual nullhomotopy of every based cube, fixing its whole boundary. -/
theorem genLoop_three_nullhomotopic (x : Space) (p : GenLoop (Fin 3) Space x) :
    GenLoop.Homotopic p GenLoop.const :=
  Quotient.exact (@Subsingleton.elim (π_ 3 Space x)
    (piThree_subsingleton x) ⟦p⟧ ⟦GenLoop.const⟧)

/-- The first three actual connectivity conditions hold for the original topology. -/
theorem space_three_connected :
    SimplyConnectedSpace Space ∧
      (∀ x : Space, Subsingleton (π_ 2 Space x)) ∧
      ∀ x : Space, Subsingleton (π_ 3 Space x) :=
  ⟨space_simplyConnected, HomotopyTwo.piTwo_subsingleton, piThree_subsingleton⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomotopyThree
