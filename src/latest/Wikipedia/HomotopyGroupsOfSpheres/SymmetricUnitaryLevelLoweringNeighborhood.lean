import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryQuantitativeCrossing
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryNoncriticalCrossing

/-!
# Quantitative lowering near every polygon above the minimum energy

Critical and noncritical polygons now have the same supported lowering
interface. The neighborhood and lowering threshold precede every subsequent
spatial tolerance and energy allowance in the quantifiers.
-/

open Set Module
open scoped Matrix.Norms.Frobenius ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open VertexSpace BalancedRealInvolutions

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {m : ℕ}

include I

theorem exists_quantitative_lowering_neighborhood (n : ℕ)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : VertexSpace.Space (Index n) m) (hv : v ∈ admissible specialIdentity (antipode n) m)
    (habove : (4 * n : ℝ) * Real.pi ^ 2 < energy specialIdentity (antipode n) τ v)
    (N : Set (VertexSpace.Space (Index n) m)) (hN : IsOpen N) (hvN : v ∈ N)
    (l ε : ℝ) (hl : l < energy specialIdentity (antipode n) τ v) (hε : 0 < ε)
      (hd : finrank ℝ B < n) :
    ∃ V : Set (VertexSpace.Space (Index n) m), IsOpen V ∧ v ∈ V ∧
      V ⊆ admissible specialIdentity (antipode n) m ∩ N ∧
      (∀ z ∈ V, l < energy specialIdentity (antipode n) τ z) ∧
      ∃ k : ℝ, l < k ∧ k < energy specialIdentity (antipode n) τ v ∧
        ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
          ∀ (p : C(M, VertexSpace.Space (Index n) m)),
            (∀ x, p x ∈ admissible specialIdentity (antipode n) m) →
            ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
              ∃ q : C(M, VertexSpace.Space (Index n) m),
                (∀ x ∈ K, energy specialIdentity (antipode n) τ (q x) < k) ∧
                ∃ G : ContinuousMap.HomotopyRel p q
                  ({x | energy specialIdentity (antipode n) τ (p x) ≤ l} ∪ (p ⁻¹' V)ᶜ),
                  ∀ t x, G (t, x) ∈ admissible specialIdentity (antipode n) m ∧
                    energy specialIdentity (antipode n) τ (G (t, x)) ≤ max
                      (energy specialIdentity (antipode n) τ (p x))
                        (energy specialIdentity (antipode n) τ v + ε) ∧
                    (G (t, x) = p x ∨ G (t, x) ∈ N) ∧
                    energy specialIdentity (antipode n) τ (G (t, x))
                      < energy specialIdentity (antipode n) τ (p x) + ξ ∧
                    (energy specialIdentity (antipode n) τ (p x)
                      - energy specialIdentity (antipode n) τ (G (t, x)) ≤ 2 * ζ →
                      dist (G (t, x)) (p x) < ρ) := by
  by_cases hcrit : fderiv ℝ (localEnergy specialIdentity (antipode n) τ v) 0 = 0
  · exact exists_quantitative_crossing_fixing_sublevel (I := I) n τ hτ hzero hone v hv
      hcrit habove N hN hvN l ε hl hε hd
  · exact exists_quantitative_noncritical_crossing specialIdentity (antipode n)
      τ v hv hcrit N hN hvN l ε hl hε

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
