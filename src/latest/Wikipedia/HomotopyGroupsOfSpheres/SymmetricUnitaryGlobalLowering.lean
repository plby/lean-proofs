import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCompactLevelLowering
import Wikipedia.NoExoticSixSphere.LoweringFromLevelCrossings

/-!
# Global lowering above the antipodal minimum energy

Every compact boundaryless parameter family in the index range can be lowered
below any target strictly above the minimum, with a prescribed lower sublevel
fixed and a fixed compact energy cap. This does not yet retract the family
onto the minimum locus or compute a symmetric-space homotopy group.
-/

open Set Module
open scoped Matrix.Norms.Frobenius ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open VertexSpace BalancedRealInvolutions FiniteControlledLowering

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {m : ℕ}

include I

theorem exists_lowering_above_minimum (n : ℕ)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (floor target cap : ℝ) (hfloor : floor < target)
    (htarget : (4 * n : ℝ) * Real.pi ^ 2 < target)
    (hcompact : IsCompact (energySublevel specialIdentity (antipode n) τ cap))
    (hd : finrank ℝ B < n)
    (p : C(M, VertexSpace.Space (Index n) m))
      (hp : ∀ x, p x ∈ admissible specialIdentity (antipode n) m)
    (start : ℝ) (hstart : start < cap)
      (hpstart : ∀ x, energy specialIdentity (antipode n) τ (p x) ≤ start) :
    ∃ q : C(M, VertexSpace.Space (Index n) m),
      (∀ x, energy specialIdentity (antipode n) τ (q x) < target) ∧
      ∃ G : ContinuousMap.HomotopyRel p q {x | energy specialIdentity (antipode n) τ (p x) ≤ floor},
        ∀ t x, G (t, x) ∈ energySublevel specialIdentity (antipode n) τ cap := by
  apply lowering_of_level_crossings (energy specialIdentity (antipode n) τ)
    (admissible specialIdentity (antipode n) m)
    floor ((4 * n : ℝ) * Real.pi ^ 2) cap target hfloor htarget ?_
    p hp start hstart hpstart
  intro level habove hfloorlevel hlevelcap
  obtain ⟨δ, hδ, _, _, hcross⟩ := exists_compact_level_crossing (I := I) (M := M)
    n τ hτ hzero hone floor level cap habove hfloorlevel hlevelcap hcompact hd
  exact ⟨δ, hδ, hcross⟩

/-- Arbitrarily fine partitions support global lowering to every target above
the minimum. Compactness and shortness are conclusions of the partition choice. -/
theorem exists_partition_with_global_lowering (n : ℕ) (cap : ℝ) (N : ℕ)
    (hd : finrank ℝ B < n) :
    ∃ m : ℕ, N ≤ m ∧
      ∀ floor target : ℝ, floor < target → (4 * n : ℝ) * Real.pi ^ 2 < target →
      ∀ p : C(M, VertexSpace.Space (Index n) m),
        (∀ x, p x ∈ admissible specialIdentity (antipode n) m) →
      ∀ start : ℝ, start < cap →
      (∀ x, energy specialIdentity (antipode n) (UniformTimePartition.time m) (p x) ≤ start) →
      ∃ q : C(M, VertexSpace.Space (Index n) m),
        (∀ x, energy specialIdentity (antipode n) (UniformTimePartition.time m) (q x) < target) ∧
        ∃ G : ContinuousMap.HomotopyRel p q
            {x | energy specialIdentity (antipode n) (UniformTimePartition.time m) (p x) ≤ floor},
          ∀ t x, G (t, x) ∈ energySublevel specialIdentity (antipode n)
              (UniformTimePartition.time m) cap := by
  obtain ⟨m, hNm, hm⟩ := exists_compact_sublevels_partition (Index n) cap N
  refine ⟨m, hNm, ?_⟩
  intro floor target hfloor htarget p hp start hstart hpstart
  exact exists_lowering_above_minimum (I := I) n (UniformTimePartition.time m)
    (UniformTimePartition.strictMono_time m) (UniformTimePartition.time_zero m)
    (UniformTimePartition.time_last m) floor target cap hfloor htarget
    (hm specialIdentity (antipode n) cap le_rfl).1 hd p hp start hstart hpstart

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
