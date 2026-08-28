import Wikipedia.NoExoticSixSphere.OrthogonalBandDeformation
import Wikipedia.NoExoticSixSphere.OrthogonalCriticalEnergySpectrum

/-!
# Sublevel homotopy equivalences between antipodal critical-energy values

Inside each open gap of the proved containing lattice for critical energies,
the actual polygon sublevels are homotopy equivalent. A sufficiently fine
common partition supplies compactness for every endpoint pair, so the final
existence theorem has no unproved noncriticality or compactness premise.

This does not compare sublevels across a critical value and does not prove
the required Bott comparison or the six-sphere classification.
-/

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m : ℕ}

theorem nonempty_sublevel_homotopyEquiv_of_gap (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (q : ℕ) (k E : ℝ) (hkE : k ≤ E)
    (hlow : ((n : ℝ) + 8 * (q : ℝ)) * Real.pi ^ 2 < k)
    (hhigh : E < ((n : ℝ) + 8 * ((q : ℝ) + 1)) * Real.pi ^ 2)
    (hcompact : IsCompact (energySublevel a b τ E)) :
    Nonempty (ContinuousMap.HomotopyEquiv (energySublevel a b τ E)
      (energySublevel a b τ k)) := by
  apply nonempty_sublevel_homotopyEquiv a b τ k E hkE hcompact
  intro v hv
  exact noncritical_of_energy_mem_gap a b τ hτ hzero hone hanti v hv.1.1 q
    (hlow.trans_le hv.2) (hv.1.2.trans_lt hhigh)

/-- The gap comparison holds on arbitrarily fine common partitions, with
compactness and absence of critical points both proved. -/
theorem exists_gap_homotopyEquiv_partition (n q N : ℕ) (k E : ℝ) (hkE : k ≤ E)
    (hlow : ((n : ℝ) + 8 * (q : ℝ)) * Real.pi ^ 2 < k)
    (hhigh : E < ((n : ℝ) + 8 * ((q : ℝ) + 1)) * Real.pi ^ 2) :
    ∃ m : ℕ, N ≤ m ∧ ∀ a b : OrthogonalOperators n,
      (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n) →
      Nonempty (ContinuousMap.HomotopyEquiv
        (energySublevel a b (UniformTimePartition.time m) E)
        (energySublevel a b (UniformTimePartition.time m) k)) := by
  obtain ⟨m, hNm, hm⟩ := exists_compact_sublevels_partition n E N
  refine ⟨m, hNm, fun a b hanti ↦ ?_⟩
  exact nonempty_sublevel_homotopyEquiv_of_gap a b (UniformTimePartition.time m)
    (UniformTimePartition.strictMono_time m) (UniformTimePartition.time_zero m)
    (UniformTimePartition.time_last m) hanti q k E hkE hlow hhigh (hm a b E le_rfl).1

end NoExoticSixSphere.OrthogonalPolygon
