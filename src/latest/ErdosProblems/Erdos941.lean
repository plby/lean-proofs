import ErdosProblems.Erdos941.EasyCases
import ErdosProblems.Erdos941.PairGeometry
import ErdosProblems.Erdos941.SiegelLowerBound
import ErdosProblems.Erdos941.Avoidance
import ErdosProblems.Erdos941.PrimitiveThreeSquares
import ErdosProblems.Erdos941.SphereQuadraticOrder
import ErdosProblems.Erdos941.RootQuaternionInjection
import ErdosProblems.Erdos941.IntertwinerArea
import ErdosProblems.Erdos941.RootCountingTransfer
import ErdosProblems.Erdos941.SphereMass
import ErdosProblems.Erdos941.Shadowing
import ErdosProblems.Erdos941.SpherePairCount
import ErdosProblems.Erdos941.ShadowPairCount
import ErdosProblems.Erdos941.ModularAvoidance
import ErdosProblems.Erdos941.DenseTrajectoryHitting
import ErdosProblems.Erdos941.FinalAssembly

/-!
# Erdős problem 941

Every sufficiently large natural number is a sum of at most three positive
powerful numbers. The proof combines integral sphere-to-form maps, a uniform
sphere lower bound, elementary shadowing, pair counting, and finite modular
avoidance. All supporting results are proved in `Erdos941/`.
-/

namespace Erdos941

/-- Every sufficiently large integer is a sum of one, two, or three positive
powerful integers. The prime-square condition is explicit in the statement. -/
theorem erdos_941 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ l : List ℕ, 1 ≤ l.length ∧ l.length ≤ 3 ∧
        (∀ a ∈ l, 0 < a ∧ ∀ p : ℕ, p.Prime → p ∣ a → p ^ 2 ∣ a) ∧ l.sum = n := by
  obtain ⟨N, _, hN⟩ := exists_eventually_representable
  exact ⟨N, hN⟩

#print axioms erdos_941

end Erdos941
