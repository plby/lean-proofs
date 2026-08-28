import Wikipedia.NoExoticSixSphere.JamesComparisonConnectivity
import Wikipedia.NoExoticSixSphere.HomotopyFiberConnectivity

/-!
# The actual James comparison fiber is simply connected

The original comparison's native second-homotopy map is identified
with the generic induced map used by the genuine fiber exact sequence.
The checked bijectivity and source/target simple connectivity give
simple connectivity of the original compact-open homotopy fiber.
Higher fiber homotopy groups are not declared trivial.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem OrbitPair

namespace NoExoticSixSphere.JamesSphere.ComparisonFiber

abbrev Space (n : ℕ) (x : WordHomology.Words n) :=
  HomotopyFiber.Space (loopComparison n) (loopComparison n x)

def basepoint (n : ℕ) (x : WordHomology.Words n) : Space n x :=
  HomotopyFiber.basepoint (loopComparison n) x

theorem native_piTwo_map (n : ℕ) (x : WordHomology.Words n) :
    HigherHomotopy.map (N := Fin 2) (loopComparison n) (y := x) rfl =
      SecondHurewicz.homotopyMap (loopComparison n) x := by
  funext a
  refine Quotient.inductionOn a fun p ↦ ?_
  rfl

theorem simplyConnectedSpace (n : ℕ) (x : WordHomology.Words (n + 2)) :
    SimplyConnectedSpace (Space (n + 2) x) := by
  let := JamesSphere.simplyConnectedSpace n
  let := ComparisonCylinder.loops_simplyConnected n
  apply HomotopyFiberConnectivity.simplyConnectedSpace (loopComparison (n + 2)) x
  rw [native_piTwo_map]
  exact (ComparisonCylinder.comparison_piTwo_bijective n x).surjective

end NoExoticSixSphere.JamesSphere.ComparisonFiber
