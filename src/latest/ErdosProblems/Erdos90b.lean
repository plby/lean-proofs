/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos90b.External.ErdosUnitDistance.Main

/-!
# Erdős Problem 90b: arbitrarily many unit distances

L. Alpöge's construction disproves every proposed uniform bound
`n ^ (1 + C / log (log n))`: for each positive constant `C` and each
cardinality threshold, there is a larger planar configuration with more
unit-distance pairs than that bound. The supporting formalization is due to
Kim Morrison and the Tau Ceti contributors.
-/

namespace Erdos90b

/-- A point of the Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The number of unordered pairs of distinct points at distance one. -/
noncomputable abbrev unitDistancePairs (P : Finset Point) : ℕ :=
  Erdos.unitDist P

/-- Alpöge's counterexamples beat every fixed constant in the proposed
unit-distance exponent, above every prescribed cardinality threshold. -/
theorem erdos_90b :
    ∀ C : ℝ, 0 < C → ∀ N : ℕ,
      ∃ (n : ℕ) (P : Finset Point),
        N ≤ n ∧ P.card = n ∧
          (n : ℝ) ^ (1 + C / Real.log (Real.log n)) <
            (unitDistancePairs P : ℝ) := by
  simpa only [unitDistancePairs] using
    Erdos.erdos_unit_distance_uniform_constant_false

#print axioms Erdos90b.erdos_90b

end Erdos90b
