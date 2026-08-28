import Wikipedia.HopfProblem.OrbitPairSphereMinimumNeighborhood
import Wikipedia.HopfProblem.OrbitPairSphereGlobalLowering

/-!
# Global relative deformation into the exact semicircle minimum locus

Global lowering first reaches a small sublevel on which the explicit minimum
retraction homotopy is controlled. Concatenation reaches the exact minimum,
fixing every parameter whose original polygon was already minimal. A uniform
partition can supply all mesh conditions and an interior sample simultaneously.
Admissibility of the original family follows from its stated energy bound.
-/

noncomputable section

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m : ℕ}

include I

theorem exists_homotopy_into_minimum (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (cap : ℝ) (hcap : Real.pi ^ 2 < cap)
    (hmesh : ∀ i : Fin (m + 1), cap * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (j : Fin m) (hd : finrank ℝ B + 2 < 2 * n)
    (p : C(M, Space n m)) (start : ℝ) (hstart : start < cap)
    (hpstart : ∀ x, energy a b τ (p x) ≤ start) :
    ∃ r : C(M, Space n m), (∀ x, r x ∈ minimumSet a b τ) ∧
      ∃ G : ContinuousMap.HomotopyRel p r (p ⁻¹' minimumSet a b τ),
        ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  have hp : ∀ x, p x ∈ admissible (costDomain n) a b m := fun x =>
    sublevel_subset_admissible a b τ hτ cap hmesh ((hpstart x).trans hstart.le)
  have hcompact := isCompact_energySublevel a b τ hτ cap hmesh
  obtain ⟨δ, hδ, _, hnear⟩ := exists_near_minimum_homotopy (M := M)
    a b τ hτ hzero hone hanti cap hcap hmesh j
  obtain ⟨q, hq, G, hG⟩ := exists_lowering_above_minimum (I := I)
    a b τ hτ hzero hone hanti (Real.pi ^ 2) (Real.pi ^ 2 + δ)
    cap (by linarith) (by linarith) hcompact hd p hp start hstart hpstart
  have hqsub (x : M) : q x ∈ energySublevel a b τ (Real.pi ^ 2 + δ) := by
    have hqa : q x ∈ admissible (costDomain n) a b m := by
      simpa only [G.apply_one] using (hG 1 x).1
    exact ⟨hqa, (hq x).le⟩
  obtain ⟨r, hr, J, hJ⟩ := hnear q hqsub
  let Gfixed : ContinuousMap.HomotopyRel p q (p ⁻¹' minimumSet a b τ) :=
    { toHomotopy := G.toHomotopy
      prop' := fun t x hx => G.eq_fst t hx.2.le }
  let Jfixed : ContinuousMap.HomotopyRel q r (p ⁻¹' minimumSet a b τ) :=
    { toHomotopy := J.toHomotopy
      prop' := by
        intro t x hx
        apply J.eq_fst t
        change q x ∈ minimumSet a b τ
        rw [← Gfixed.fst_eq_snd hx]
        exact hx }
  refine ⟨r, hr, Gfixed.trans Jfixed, ?_⟩
  intro t x
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact hG _ x
  · exact hJ _ x

/-- The uniform partition is chosen before the endpoint pair and family.
No separate compactness, critical-point, or local-deformation input remains. -/
theorem exists_partition_with_minimum_deformation (n : ℕ) (cap : ℝ)
    (hcap : Real.pi ^ 2 < cap) (N : ℕ) (hd : finrank ℝ B + 2 < 2 * n) :
    ∃ m : ℕ, N ≤ m ∧ 0 < m ∧
      (∀ i : Fin (m + 1), cap * (UniformTimePartition.time m i.succ -
        UniformTimePartition.time m i.castSucc) < Real.pi ^ 2) ∧
      ∀ a b : Sphere n, b.val = -a.val →
      ∀ p : C(M, Space n m), ∀ start : ℝ, start < cap →
      (∀ x, energy a b (UniformTimePartition.time m) (p x) ≤ start) →
      ∃ r : C(M, Space n m),
        (∀ x, r x ∈ minimumSet a b (UniformTimePartition.time m)) ∧
        ∃ G : ContinuousMap.HomotopyRel p r (p ⁻¹' minimumSet a b (UniformTimePartition.time m)),
          ∀ t x, G (t, x) ∈ energySublevel a b (UniformTimePartition.time m) cap := by
  obtain ⟨m, hNm, hmesh, _⟩ := exists_compact_sublevels_partition n cap (max N 1)
  have hpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hNm)
  refine ⟨m, (le_max_left N 1).trans hNm, hpos, hmesh, ?_⟩
  intro a b hanti p start hstart hpstart
  exact exists_homotopy_into_minimum (I := I) a b (UniformTimePartition.time m)
    (UniformTimePartition.strictMono_time m) (UniformTimePartition.time_zero m)
    (UniformTimePartition.time_last m) hanti cap hcap hmesh ⟨0, hpos⟩ hd p start hstart hpstart

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
