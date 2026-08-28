import Wikipedia.NoExoticSixSphere.CompactLevelLowering
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryLoweringData
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonSublevels

/-!
# Crossing an entire compact level of antipodal polygon energy

The local critical and noncritical constructions are assembled over the whole
energy level. The result preserves a prescribed lower sublevel and stays in
the chosen compact short sublevel throughout the homotopy.
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

theorem exists_compact_level_crossing (n : ℕ)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (floor level cap : ℝ) (habove : (4 * n : ℝ) * Real.pi ^ 2 < level)
    (hfloor : floor < level) (hcap : level < cap)
    (hcompact : IsCompact (energySublevel specialIdentity (antipode n) τ cap))
    (hd : finrank ℝ B < n) :
    ∃ δ > 0, floor < level - δ ∧ level + δ < cap ∧
      ∀ p : C(M, VertexSpace.Space (Index n) m),
        (∀ x, p x ∈ admissible specialIdentity (antipode n) m) →
      (∀ x, energy specialIdentity (antipode n) τ (p x) ≤ level + δ / 4) →
      ∃ q : C(M, VertexSpace.Space (Index n) m),
        (∀ x, energy specialIdentity (antipode n) τ (q x) < level - δ / 2) ∧
        ∃ G : ContinuousMap.HomotopyRel p q
          {x | energy specialIdentity (antipode n) τ (p x) ≤ floor},
          ∀ t x, G (t, x) ∈ energySublevel specialIdentity (antipode n) τ cap := by
  have : CompactSpace (VertexSpace.Space (Index n) m) := inferInstance
  have hlocalCompact : LocallyCompactSpace (VertexSpace.Space (Index n) m) :=
    WeaklyLocallyCompactSpace.locallyCompactSpace
  apply @exists_compact_level_lowering M (VertexSpace.Space (Index n) m)
    _ _ inferInstance inferInstance hlocalCompact
    (energy specialIdentity (antipode n) τ)
    (admissible specialIdentity (antipode n) m)
    (continuousOn_energy specialIdentity (antipode n) τ)
      (energySublevel specialIdentity (antipode n) τ cap) hcompact
    (fun _ hv ↦ hv.1) floor level cap hfloor hcap (fun _ hv he ↦ ⟨hv, he⟩)
  intro v hv he
  change energy specialIdentity (antipode n) τ v = level at he
  have habove' : (4 * n : ℝ) * Real.pi ^ 2 < energy specialIdentity (antipode n) τ v := by rwa [he]
  have hfloor' : floor < energy specialIdentity (antipode n) τ v := by rwa [he]
  have hε : 0 < cap - level := sub_pos.mpr hcap
  have hdata := exists_localLoweringData (I := I) (M := M) n τ hτ hzero hone
    v hv.1 habove' floor (cap - level) hfloor' hε hd
  have hecap : level + (cap - level) = cap := by ring
  rw [he, hecap] at hdata
  exact hdata

/-- A single sufficiently fine partition supports crossings of every level
between the minimum energy and the chosen cap. -/
theorem exists_partition_with_level_crossings (n : ℕ) (cap : ℝ) (N : ℕ)
    (hd : finrank ℝ B < n) :
    ∃ m : ℕ, N ≤ m ∧
      ∀ floor level : ℝ, (4 * n : ℝ) * Real.pi ^ 2 < level → floor < level → level < cap →
      ∃ δ > 0, floor < level - δ ∧ level + δ < cap ∧
        ∀ p : C(M, VertexSpace.Space (Index n) m),
          (∀ x, p x ∈ admissible specialIdentity (antipode n) m) →
        (∀ x, energy specialIdentity (antipode n)
          (UniformTimePartition.time m) (p x) ≤ level + δ / 4) →
        ∃ q : C(M, VertexSpace.Space (Index n) m),
          (∀ x, energy specialIdentity (antipode n)
            (UniformTimePartition.time m) (q x) < level - δ / 2) ∧
          ∃ G : ContinuousMap.HomotopyRel p q
              {x | energy specialIdentity (antipode n) (UniformTimePartition.time m) (p x) ≤ floor},
            ∀ t x, G (t, x) ∈ energySublevel specialIdentity (antipode n)
              (UniformTimePartition.time m) cap := by
  obtain ⟨m, hNm, hm⟩ := exists_compact_sublevels_partition (Index n) cap N
  refine ⟨m, hNm, ?_⟩
  intro floor level habove hfloor hcap
  exact exists_compact_level_crossing (I := I) n (UniformTimePartition.time m)
    (UniformTimePartition.strictMono_time m) (UniformTimePartition.time_zero m)
    (UniformTimePartition.time_last m) floor level cap habove hfloor hcap
    (hm specialIdentity (antipode n) cap le_rfl).1 hd

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
