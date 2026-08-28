import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumNeighborhoodHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryGlobalLowering

/-!
# Deformation into balanced minimum polygons

Global lowering reaches the controlled neighborhood of the minimum locus.
The neighborhood homotopy then reaches the exact minimum, with every original
minimum polygon fixed throughout. The parameter dimension is strictly less
than the balanced rank, as required by the negative Hessian construction.
-/

open Set Module
open scoped Matrix.Norms.Frobenius ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open NoExoticSixSphere VertexSpace BalancedRealInvolutions ComplexSkewMatrices

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {m : ℕ}

include I

theorem exists_homotopy_into_minimum (n : ℕ)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hsmall : ∀ J : BalancedRealInvolutions.Space n, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) • imaginaryDirection (minimumGenerator J)‖ <
        CompatibleLog.radius (Index n))
    (cap : ℝ) (hcap : (4 * n : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel specialIdentity (antipode n) τ cap))
    (hd : finrank ℝ B < n)
    (p : C(M, VertexSpace.Space (Index n) m))
    (hp : ∀ x, p x ∈ admissible specialIdentity (antipode n) m)
    (start : ℝ) (hstart : start < cap)
    (hpstart : ∀ x, energy specialIdentity (antipode n) τ (p x) ≤ start) :
    ∃ r : C(M, VertexSpace.Space (Index n) m), (∀ x, r x ∈ minimumSet n τ) ∧
      ∃ G : ContinuousMap.HomotopyRel p r (p ⁻¹' minimumSet n τ),
        ∀ t x, G (t, x) ∈ energySublevel specialIdentity (antipode n) τ cap := by
  obtain ⟨δ, hδ, _, hnear⟩ := exists_near_minimum_homotopy (M := M)
    n τ hτ hzero hone hsmall cap hcap hcompact
  obtain ⟨q, hq, G, hG⟩ := exists_lowering_above_minimum (I := I)
    n τ hτ hzero hone ((4 * n : ℝ) * Real.pi ^ 2)
    ((4 * n : ℝ) * Real.pi ^ 2 + δ)
    cap (by linarith) (by linarith) hcompact hd p hp start hstart hpstart
  have hqsub (x : M) : q x ∈ energySublevel specialIdentity (antipode n) τ
      ((4 * n : ℝ) * Real.pi ^ 2 + δ) := by
    have hqa : q x ∈ admissible specialIdentity (antipode n) m := by
      simpa only [G.apply_one] using (hG 1 x).1
    exact ⟨hqa, (hq x).le⟩
  obtain ⟨r, hr, J, hJ⟩ := hnear q hqsub
  let Gfixed : ContinuousMap.HomotopyRel p q (p ⁻¹' minimumSet n τ) :=
    { toHomotopy := G.toHomotopy
      prop' := fun t x hx ↦ G.eq_fst t hx.2.le }
  let Jfixed : ContinuousMap.HomotopyRel q r (p ⁻¹' minimumSet n τ) :=
    { toHomotopy := J.toHomotopy
      prop' := by
        intro t x hx
        apply J.eq_fst t
        change q x ∈ minimumSet n τ
        rw [← Gfixed.fst_eq_snd hx]
        exact hx }
  refine ⟨r, hr, Gfixed.trans Jfixed, ?_⟩
  intro t x
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact hG _ x
  · exact hJ _ x

/-- A sufficiently fine partition supplies both the compact sublevels and
the short minimum increments, before the parameter family is chosen. -/
theorem exists_partition_with_minimum_deformation (n : ℕ) (cap : ℝ)
    (hcap : (4 * n : ℝ) * Real.pi ^ 2 < cap) (lower : ℕ) (hd : finrank ℝ B < n) :
    ∃ m : ℕ, lower ≤ m ∧
      ∀ p : C(M, VertexSpace.Space (Index n) m),
        (∀ x, p x ∈ admissible specialIdentity (antipode n) m) →
        ∀ start : ℝ, start < cap →
        (∀ x, energy specialIdentity (antipode n) (UniformTimePartition.time m) (p x) ≤ start) →
        ∃ r : C(M, VertexSpace.Space (Index n) m),
          (∀ x, r x ∈ minimumSet n (UniformTimePartition.time m)) ∧
          ∃ G : ContinuousMap.HomotopyRel p r
            (p ⁻¹' minimumSet n (UniformTimePartition.time m)),
            ∀ t x, G (t, x) ∈ energySublevel specialIdentity (antipode n)
              (UniformTimePartition.time m) cap := by
  obtain ⟨m, hm, hsmall, hcompact⟩ := exists_minimum_partition n cap lower
  refine ⟨m, hm, ?_⟩
  intro p hp start hstart hpstart
  exact exists_homotopy_into_minimum (I := I) n (UniformTimePartition.time m)
    (UniformTimePartition.strictMono_time m) (UniformTimePartition.time_zero m)
    (UniformTimePartition.time_last m) hsmall cap hcap (hcompact cap (le_max_left _ _))
    hd p hp start hstart hpstart

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
