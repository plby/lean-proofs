import Wikipedia.NoExoticSixSphere.MinimumNeighborhoodHomotopy
import Wikipedia.NoExoticSixSphere.OrthogonalGlobalLowering
import Wikipedia.NoExoticSixSphere.OrthogonalMinimumPolygonPartition

/-!
# Deforming an admissible polygon family into the exact minimum locus

Global lowering first reaches the small sublevel on which the neighborhood
retraction homotopy is controlled. Concatenation then reaches the exact minimum
set, fixing every parameter whose original polygon was already a minimum.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m : ℕ}

include I

theorem exists_homotopy_into_minimum (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hsmall : ∀ J : OrthogonalComplexStructures.Space n, ∀ i : Fin (m + 1),
      (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ (logarithmChart n).target)
    (cap : ℝ) (hcap : (n : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel a b τ cap))
    (hshort : energySublevel a b τ cap ⊆ shortDomain a b m)
    (hd : finrank ℝ B + 2 < n)
    (p : C(M, Space n m)) (hp : ∀ x, p x ∈ admissible a b m)
    (start : ℝ) (hstart : start < cap) (hpstart : ∀ x, energy a b τ (p x) ≤ start) :
    ∃ r : C(M, Space n m), (∀ x, r x ∈ minimumSet a b τ) ∧
      ∃ H : ContinuousMap.HomotopyRel p r (p ⁻¹' minimumSet a b τ),
        ∀ t x, H (t, x) ∈ energySublevel a b τ cap := by
  obtain ⟨δ, hδ, _, hnear⟩ := exists_near_minimum_homotopy (M := M)
    a b τ hτ hzero hone hanti hsmall cap hcap hcompact
  obtain ⟨q, hq, G, hG⟩ := exists_lowering_above_minimum (I := I)
    a b τ hτ hzero hone hanti ((n : ℝ) * Real.pi ^ 2) ((n : ℝ) * Real.pi ^ 2 + δ)
    cap (by linarith) (by linarith) hcompact hshort hd p hp start hstart hpstart
  have hqsub (x : M) : q x ∈ energySublevel a b τ ((n : ℝ) * Real.pi ^ 2 + δ) := by
    have hqa : q x ∈ admissible a b m := by
      simpa only [G.apply_one] using (hG 1 x).1
    exact ⟨hqa, (hq x).le⟩
  obtain ⟨r, hr, J, hJ⟩ := hnear q hqsub
  let Gfixed : ContinuousMap.HomotopyRel p q (p ⁻¹' minimumSet a b τ) :=
    { toHomotopy := G.toHomotopy
      prop' := fun t x hx ↦ G.eq_fst t hx.2.le }
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

/-- All geometric partition conditions are supplied simultaneously, for every
endpoint pair and every later family obeying the specified energy bound. -/
theorem exists_partition_with_minimum_deformation (n : ℕ) (cap : ℝ)
    (hcap : (n : ℝ) * Real.pi ^ 2 < cap) (N : ℕ) (hd : finrank ℝ B + 2 < n) :
    ∃ m : ℕ, N ≤ m ∧ ∀ a b : OrthogonalOperators n,
      (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n) →
      ∀ p : C(M, Space n m), (∀ x, p x ∈ admissible a b m) →
      ∀ start : ℝ, start < cap →
      (∀ x, energy a b (UniformTimePartition.time m) (p x) ≤ start) →
      ∃ r : C(M, Space n m), (∀ x, r x ∈ minimumSet a b (UniformTimePartition.time m)) ∧
        ∃ G : ContinuousMap.HomotopyRel p r (p ⁻¹' minimumSet a b (UniformTimePartition.time m)),
          ∀ t x, G (t, x) ∈ energySublevel a b (UniformTimePartition.time m) cap := by
  obtain ⟨m, hNm, hlevels, _, hsmall⟩ := exists_minimumPolygon_partition_control n cap N
  refine ⟨m, hNm, ?_⟩
  intro a b hanti p hp start hstart hpstart
  exact exists_homotopy_into_minimum (I := I) a b (UniformTimePartition.time m)
    (UniformTimePartition.strictMono_time m) (UniformTimePartition.time_zero m)
    (UniformTimePartition.time_last m) hanti hsmall cap hcap
    (hlevels a b cap le_rfl).1 (hlevels a b cap le_rfl).2 hd p hp start hstart hpstart

end NoExoticSixSphere.OrthogonalPolygon
