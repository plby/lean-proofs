import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryDefiningFunction
import Wikipedia.NoExoticSixSphere.ManifoldScalarDifferentialSum

/-!
# Regularity and outward sign of the global boundary equation

On the boundary every local defining function vanishes, so derivatives of
the partition weights contribute zero. The remaining weighted differentials
are all nonpositive on the actual outward vector, with a strictly negative
term at every point.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def weightedPieceLevelDifferential (i : Piece) (p : ambientSet A) :
    (ℝ × Vector 6) →L[ℝ] ℝ :=
  letI := traceChartedSpace A
  mvfderiv (ProductHalfSpace.model (Vector 6)) (weightedPieceLevel A i) p

theorem weightedPieceLevelDifferential_boundary (i : Piece) (p : Boundary A) :
    letI := traceChartedSpace A;
    weightedPieceLevelDifferential A i p.val =
      boundaryPartition A i p.val • extendedPieceLevelDifferential A i p.val := by
  let := traceChartedSpace A
  let ρ := boundaryPartition A
  by_cases hp : p.val ∈ tsupport (ρ i)
  · have hg := (contMDiffAt_extendedPieceLevel A i
      ⟨p.val, boundaryPartition_subordinate A i hp⟩).mdifferentiableAt (by simp)
    have hd := mvfderiv_mul ((ρ i).contMDiff.mdifferentiableAt (by simp)) hg
    rw [extendedPieceLevel_zero_boundary A i p, zero_smul, add_zero] at hd
    exact hd
  · have hρ : (ρ i : ambientSet A → ℝ) =ᶠ[𝓝 p.val] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hp
    have hz : ρ i p.val = 0 := hρ.eq_of_nhds
    have he : weightedPieceLevel A i =ᶠ[𝓝 p.val] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [hρ] with q hq
      change ρ i q * extendedPieceLevel A i q = 0
      change ρ i q = 0 at hq
      rw [hq, zero_mul]
    rw [show boundaryPartition A i p.val = 0 from hz, zero_smul]
    have hd := he.mfderiv_eq (I := ProductHalfSpace.model (Vector 6)) (I' := 𝓘(ℝ, ℝ))
    rw [mfderiv_const] at hd
    exact hd

def boundaryDefiningDifferential (p : ambientSet A) : (ℝ × Vector 6) →L[ℝ] ℝ :=
  letI := traceChartedSpace A
  mvfderiv (ProductHalfSpace.model (Vector 6)) (boundaryDefiningFunction A) p

theorem boundaryDefiningDifferential_eq (p : Boundary A) : letI := traceChartedSpace A;
    letI := pieceFintype;
    boundaryDefiningDifferential A p.val =
      ∑ i, boundaryPartition A i p.val • extendedPieceLevelDifferential A i p.val := by
  let := traceChartedSpace A
  let := pieceFintype
  have he : boundaryDefiningFunction A = ∑ i, weightedPieceLevel A i := by
    funext q
    simp only [boundaryDefiningFunction, Finset.sum_apply]
  have hd := mvfderiv_finset_sum Finset.univ (weightedPieceLevel A) p.val
    (fun i _ ↦ (contMDiff_weightedPieceLevel A i).mdifferentiableAt (by simp))
  rw [← he] at hd
  change boundaryDefiningDifferential A p.val = ∑ i, weightedPieceLevelDifferential A i p.val at hd
  rw [hd]
  exact Finset.sum_congr rfl (fun i _ ↦ weightedPieceLevelDifferential_boundary A i p)

theorem boundaryDefiningDifferential_outward (p : Boundary A) :
    boundaryDefiningDifferential A p.val (outwardTraceVector A p) < 0 := by
  let := traceChartedSpace A
  let := pieceFintype
  rw [boundaryDefiningDifferential_eq]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_neg'
  · intro i _
    by_cases hi : boundaryPartition A i p.val = 0
    · rw [hi, zero_mul]
    · have hp : p.val ∈ pieceDomain A i := boundaryPartition_subordinate A i
        (subset_tsupport (boundaryPartition A i) hi)
      exact mul_nonpos_of_nonneg_of_nonpos ((boundaryPartition A).nonneg i p.val)
        (extendedPieceLevelDifferential_outward A i p hp).le
  · obtain ⟨i, hi⟩ := (boundaryPartition A).exists_pos_of_mem (mem_univ p.val)
    have hp : p.val ∈ pieceDomain A i := boundaryPartition_subordinate A i
      (subset_tsupport (boundaryPartition A i) hi.ne')
    exact ⟨i, Finset.mem_univ i,
      mul_neg_of_pos_of_neg hi (extendedPieceLevelDifferential_outward A i p hp)⟩

theorem boundaryDefiningDifferential_surjective (p : Boundary A) :
    Surjective (boundaryDefiningDifferential A p.val) := by
  have hn := (boundaryDefiningDifferential_outward A p).ne
  intro y
  refine ⟨(y / boundaryDefiningDifferential A p.val (outwardTraceVector A p)) •
    outwardTraceVector A p, ?_⟩
  rw [map_smul]
  change (y / boundaryDefiningDifferential A p.val (outwardTraceVector A p)) *
    boundaryDefiningDifferential A p.val (outwardTraceVector A p) = y
  exact div_mul_cancel₀ y hn

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
