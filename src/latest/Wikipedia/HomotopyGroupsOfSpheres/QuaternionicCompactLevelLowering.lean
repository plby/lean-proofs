import Wikipedia.NoExoticSixSphere.CompactLevelLowering
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicLoweringData
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonSublevels

/-!
# Crossing an entire compact level of antipodal polygon energy

The local critical and noncritical constructions are assembled over the whole
energy level. The result preserves a prescribed lower sublevel and stays in
the chosen compact short sublevel throughout the homotopy.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization VertexSpace FiniteControlledLowering

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m : ℕ}

include I

theorem exists_compact_level_crossing (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (floor level cap : ℝ) (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < level)
    (hfloor : floor < level) (hcap : level < cap)
    (hcompact : IsCompact (energySublevel a b τ cap))
    (hshort : energySublevel a b τ cap ⊆ shortDomain a b m)
    (hd : finrank ℝ B < n) :
    ∃ δ > 0, floor < level - δ ∧ level + δ < cap ∧
      ∀ p : C(M, Space n m), (∀ x, p x ∈ admissible a b m) →
      (∀ x, energy a b τ (p x) ≤ level + δ / 4) →
      ∃ q : C(M, Space n m), (∀ x, energy a b τ (q x) < level - δ / 2) ∧
        ∃ G : ContinuousMap.HomotopyRel p q {x | energy a b τ (p x) ≤ floor},
          ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  apply exists_compact_level_lowering (energy a b τ) (admissible a b m)
    (contMDiffOn_energy a b τ).continuousOn (energySublevel a b τ cap) hcompact
    (fun _ hv ↦ hv.1) floor level cap hfloor hcap (fun _ hv he ↦ ⟨hv, he⟩)
  intro v hv he
  change energy a b τ v = level at he
  have habove' : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v := by rwa [he]
  have hfloor' : floor < energy a b τ v := by rwa [he]
  have hε : 0 < cap - level := sub_pos.mpr hcap
  have hdata := exists_localLoweringData (I := I) (M := M) a b τ hτ hzero hone
    v (hshort hv) hanti habove' floor (cap - level) hfloor' hε hd
  have hecap : level + (cap - level) = cap := by ring
  rw [he, hecap] at hdata
  exact hdata

/-- A single sufficiently fine partition supports crossings of every level
between the minimum energy and the chosen cap. -/
theorem exists_partition_with_level_crossings (n : ℕ) (cap : ℝ) (N : ℕ)
    (hd : finrank ℝ B < n) :
    ∃ m : ℕ, N ≤ m ∧ ∀ a b : symplecticSubgroup n,
      (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) →
      ∀ floor level : ℝ, ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < level → floor < level → level < cap →
      ∃ δ > 0, floor < level - δ ∧ level + δ < cap ∧
        ∀ p : C(M, Space n m), (∀ x, p x ∈ admissible a b m) →
        (∀ x, energy a b (UniformTimePartition.time m) (p x) ≤ level + δ / 4) →
        ∃ q : C(M, Space n m),
          (∀ x, energy a b (UniformTimePartition.time m) (q x) < level - δ / 2) ∧
          ∃ G : ContinuousMap.HomotopyRel p q
              {x | energy a b (UniformTimePartition.time m) (p x) ≤ floor},
            ∀ t x, G (t, x) ∈ energySublevel a b (UniformTimePartition.time m) cap := by
  obtain ⟨m, hNm, hm⟩ := exists_compact_sublevels_partition n cap N
  refine ⟨m, hNm, ?_⟩
  intro a b hanti floor level habove hfloor hcap
  exact exists_compact_level_crossing (I := I) a b (UniformTimePartition.time m)
    (UniformTimePartition.strictMono_time m) (UniformTimePartition.time_zero m)
    (UniformTimePartition.time_last m) hanti floor level cap habove hfloor hcap
    (hm a b cap le_rfl).1 (hm a b cap le_rfl).2 hd

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
