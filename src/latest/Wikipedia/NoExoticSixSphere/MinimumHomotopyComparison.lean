import Wikipedia.NoExoticSixSphere.MinimumHomotopyReflection

/-!
# The minimum inclusion reflects relative homotopy

For a sublevel strictly below the controlled cap, two maps into the minimum
locus become relatively homotopic after inclusion if and only if they already
were relatively homotopic. All spaces and inclusions are the actual polygon
spaces, with their subspace topologies.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace

variable {n m : ℕ}

noncomputable def minimumSublevelInclusion (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (E : ℝ) (hE : (n : ℝ) * Real.pi ^ 2 ≤ E) :
    C(minimumSet a b τ, energySublevel a b τ E) where
  toFun v := ⟨v.1, v.2.1, by rw [v.2.2]; exact hE⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I

theorem minimumHomotopicRel_iff_sublevel (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hsmall : ∀ J : OrthogonalComplexStructures.Space n, ∀ i : Fin (m + 1),
      (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ (logarithmChart n).target)
    (cap : ℝ) (hcap : (n : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel a b τ cap))
    (hshort : energySublevel a b τ cap ⊆ shortDomain a b m)
    (hd : finrank ℝ B + 3 < n)
    (E : ℝ) (hE : (n : ℝ) * Real.pi ^ 2 ≤ E) (hEcap : E < cap)
    (f g : C(M, minimumSet a b τ)) (S : Set M) :
    ContinuousMap.HomotopicRel f g S ↔
      ContinuousMap.HomotopicRel ((minimumSublevelInclusion a b τ E hE).comp f)
        ((minimumSublevelInclusion a b τ E hE).comp g) S := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.compContinuousMap (minimumSublevelInclusion a b τ E hE)⟩
  · rintro ⟨F⟩
    let inc : C(energySublevel a b τ E, Space n m) := ⟨Subtype.val, continuous_subtype_val⟩
    let Fambient : ContinuousMap.HomotopyRel ((minimumInclusion a b τ).comp f)
        ((minimumInclusion a b τ).comp g) S := F.compContinuousMap inc
    exact nonempty_minimumHomotopyRel_of_ambient (I := I)
      a b τ hτ hzero hone hanti hsmall cap hcap hcompact hshort hd f g S Fambient
      (fun t x ↦ (F (t, x)).2.1) E hEcap (fun t x ↦ (F (t, x)).2.2)

/-- A common arbitrarily fine partition gives the relative homotopy comparison
for every endpoint pair, every intermediate sublevel, and every later pair of maps. -/
theorem exists_partition_with_minimumHomotopy_comparison (n : ℕ) (cap : ℝ)
    (hcap : (n : ℝ) * Real.pi ^ 2 < cap) (N : ℕ) (hd : finrank ℝ B + 3 < n) :
    ∃ m : ℕ, N ≤ m ∧ ∀ a b : OrthogonalOperators n,
      (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n) →
      ∀ E : ℝ, ∀ hE : (n : ℝ) * Real.pi ^ 2 ≤ E, E < cap →
      ∀ f g : C(M, minimumSet a b (UniformTimePartition.time m)), ∀ S : Set M,
        ContinuousMap.HomotopicRel f g S ↔
          ContinuousMap.HomotopicRel
            ((minimumSublevelInclusion a b (UniformTimePartition.time m) E hE).comp f)
            ((minimumSublevelInclusion a b (UniformTimePartition.time m) E hE).comp g) S := by
  obtain ⟨m, hNm, hlevels, _, hsmall⟩ := exists_minimumPolygon_partition_control n cap N
  refine ⟨m, hNm, ?_⟩
  intro a b hanti E hE hEcap f g S
  exact minimumHomotopicRel_iff_sublevel (I := I) a b (UniformTimePartition.time m)
    (UniformTimePartition.strictMono_time m) (UniformTimePartition.time_zero m)
    (UniformTimePartition.time_last m) hanti hsmall cap hcap
    (hlevels a b cap le_rfl).1 (hlevels a b cap le_rfl).2 hd E hE hEcap f g S

end NoExoticSixSphere.OrthogonalPolygon
