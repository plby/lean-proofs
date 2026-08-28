import Wikipedia.HopfProblem.OrbitPairSphereCompactLevelLowering
import Wikipedia.NoExoticSixSphere.LoweringFromLevelCrossings

/-!
# Global lowering above the antipodal minimum energy

Every compact boundaryless parameter family in the index range can be lowered
below any target strictly above the minimum, with a prescribed lower sublevel
fixed and a fixed compact energy cap. This does not yet retract the family
onto the minimum locus or compute a sphere homotopy group.
-/

noncomputable section

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace FiniteControlledLowering

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m : ℕ}

include I

theorem exists_lowering_above_minimum (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val)
    (floor target cap : ℝ) (hfloor : floor < target)
    (htarget : Real.pi ^ 2 < target)
    (hcompact : IsCompact (energySublevel a b τ cap))
    (hd : finrank ℝ B + 2 < 2 * n)
    (p : C(M, Space n m)) (hp : ∀ x, p x ∈ admissible (costDomain n) a b m)
    (start : ℝ) (hstart : start < cap) (hpstart : ∀ x, energy a b τ (p x) ≤ start) :
    ∃ q : C(M, Space n m), (∀ x, energy a b τ (q x) < target) ∧
      ∃ G : ContinuousMap.HomotopyRel p q {x | energy a b τ (p x) ≤ floor},
        ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  apply lowering_of_level_crossings (energy a b τ) (admissible (costDomain n) a b m)
    floor (Real.pi ^ 2) cap target hfloor htarget ?_ p hp start hstart hpstart
  intro level habove hfloorlevel hlevelcap
  obtain ⟨δ, hδ, _, _, hcross⟩ := exists_compact_level_crossing (I := I) (M := M)
    a b τ hτ hzero hone hanti floor level cap habove hfloorlevel hlevelcap hcompact hd
  exact ⟨δ, hδ, hcross⟩

/-- Arbitrarily fine partitions support global lowering to every target above
the minimum. Compactness and shortness are conclusions of the partition choice. -/
theorem exists_partition_with_global_lowering (n : ℕ) (cap : ℝ) (N : ℕ)
    (hd : finrank ℝ B + 2 < 2 * n) :
    ∃ m : ℕ, N ≤ m ∧ ∀ a b : Sphere n,
      b.val = -a.val →
      ∀ floor target : ℝ, floor < target → Real.pi ^ 2 < target →
      ∀ p : C(M, Space n m), (∀ x, p x ∈ admissible (costDomain n) a b m) →
      ∀ start : ℝ, start < cap →
      (∀ x, energy a b (UniformTimePartition.time m) (p x) ≤ start) →
      ∃ q : C(M, Space n m), (∀ x, energy a b (UniformTimePartition.time m) (q x) < target) ∧
        ∃ G : ContinuousMap.HomotopyRel p q
            {x | energy a b (UniformTimePartition.time m) (p x) ≤ floor},
          ∀ t x, G (t, x) ∈ energySublevel a b (UniformTimePartition.time m) cap := by
  obtain ⟨m, hNm, _, hm⟩ := exists_compact_sublevels_partition n cap N
  refine ⟨m, hNm, ?_⟩
  intro a b hanti floor target hfloor htarget p hp start hstart hpstart
  exact exists_lowering_above_minimum (I := I) a b (UniformTimePartition.time m)
    (UniformTimePartition.strictMono_time m) (UniformTimePartition.time_zero m)
    (UniformTimePartition.time_last m) hanti floor target cap hfloor htarget
    (hm a b cap le_rfl).1 hd p hp start hstart hpstart

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
