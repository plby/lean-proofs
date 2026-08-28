import Wikipedia.HopfProblem.ThreefoldHomologySecondVanishing
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnected
import Wikipedia.HopfProblem.ThreefoldFundamentalGroup

/-!
# The actual second homotopy group of the constructed threefold is trivial

Native simple connectedness and the proved original second Hurewicz
isomorphism identify the actual based-square homotopy group with the
genuine second integral homology. That group has now been proved zero
from the original attachment maps and central circle sweeps. Thus every
original based square is nullhomotopic relative to its full boundary.
No sphere identification or higher Hurewicz theorem is used.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomotopyTwo

open SingularMayerVietoris

/-- The original second Hurewicz map for the actual constructed threefold. -/
def hurewiczEquiv (x : Space) : Additive (π_ 2 Space x) ≃ₗ[ℤ] SingularHomology Space 2 := by
  letI := space_simplyConnected
  exact SecondHurewicz.SimplyConnected.hurewiczLinearEquiv x

@[simp] theorem hurewiczEquiv_toLinearMap (x : Space) :
    (hurewiczEquiv x).toLinearMap = SecondHurewicz.hurewiczMap x := rfl

/-- The forward map is still the genuine singular cycle of the original based square. -/
@[simp] theorem hurewiczEquiv_mk (x : Space) (p : GenLoop (Fin 2) Space x) :
    hurewiczEquiv x (Additive.ofMul (⟦p⟧ : π_ 2 Space x)) =
      SecondHurewicz.squareHomologyClass p := rfl

/-- At every actual base point the native second homotopy group is trivial. -/
theorem piTwo_subsingleton (x : Space) : Subsingleton (π_ 2 Space x) := by
  have := space_simplyConnected
  have := Homology.SecondDegree.homologyTwo_subsingleton
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton

theorem piTwo_eq_one (x : Space) (a : π_ 2 Space x) : a = 1 :=
  (piTwo_subsingleton x).elim _ _

theorem additive_piTwo_eq_zero (x : Space) (a : Additive (π_ 2 Space x)) : a = 0 := by
  have := piTwo_subsingleton x
  exact Subsingleton.elim _ _

/-- Actual relative-boundary nullhomotopy, not merely a rank or abstract group calculation. -/
theorem genLoop_two_nullhomotopic (x : Space) (p : GenLoop (Fin 2) Space x) :
    GenLoop.Homotopic p GenLoop.const :=
  Quotient.exact (@Subsingleton.elim (π_ 2 Space x)
    (piTwo_subsingleton x) ⟦p⟧ ⟦GenLoop.const⟧)

/-- The original topology satisfies the first two native homotopy vanishing statements. -/
theorem space_two_connected :
    SimplyConnectedSpace Space ∧ ∀ x : Space, Subsingleton (π_ 2 Space x) :=
  ⟨space_simplyConnected, piTwo_subsingleton⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HomotopyTwo
