import Wikipedia.NoExoticSixSphere.RoundedTraceDefiningExtensions
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# A global smooth function defining the actual native boundary

A smooth partition of unity is subordinate to the three actual open pieces.
Its weighted sum of the nonnegative local equations is smooth globally,
nonnegative, and zero exactly on the native manifold boundary.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem exists_boundaryPartition : letI := traceChartedSpace A;
    ∃ ρ : SmoothPartitionOfUnity Piece (ProductHalfSpace.model (Vector 6)) (ambientSet A),
      ρ.IsSubordinate (fun i ↦ (pieceDomain A i : Set (ambientSet A))) := by
  let := traceChartedSpace A
  let := trace_isManifold A
  let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
  apply SmoothPartitionOfUnity.exists_isSubordinate (ProductHalfSpace.model (Vector 6))
    isClosed_univ _
    (fun i ↦ (pieceDomain A i).isOpen)
  intro p _
  obtain ⟨i, hi⟩ := pieceDomain_covers A p
  exact mem_iUnion.mpr ⟨i, hi⟩

def boundaryPartition : letI := traceChartedSpace A;
    SmoothPartitionOfUnity Piece (ProductHalfSpace.model (Vector 6)) (ambientSet A) :=
  Classical.choose (exists_boundaryPartition A)

theorem boundaryPartition_subordinate : letI := traceChartedSpace A;
    (boundaryPartition A).IsSubordinate (fun i ↦ (pieceDomain A i : Set (ambientSet A))) :=
  Classical.choose_spec (exists_boundaryPartition A)

def weightedPieceLevel (i : Piece) (p : ambientSet A) : ℝ :=
  letI := traceChartedSpace A
  boundaryPartition A i p * extendedPieceLevel A i p

theorem weightedPieceLevel_nonneg (i : Piece) (p : ambientSet A) :
    0 ≤ weightedPieceLevel A i p := by
  let := traceChartedSpace A
  exact mul_nonneg ((boundaryPartition A).nonneg i p) (extendedPieceLevel_nonneg A i p)

theorem contMDiff_weightedPieceLevel (i : Piece) : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, ℝ) ∞ (weightedPieceLevel A i) := by
  let := traceChartedSpace A
  exact (boundaryPartition A).contMDiff_smul (i := i) (fun p hp ↦
    contMDiffAt_extendedPieceLevel A i ⟨p, boundaryPartition_subordinate A i hp⟩)

def boundaryDefiningFunction (p : ambientSet A) : ℝ :=
  letI := pieceFintype
  ∑ i, weightedPieceLevel A i p

theorem contMDiff_boundaryDefiningFunction : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, ℝ) ∞ (boundaryDefiningFunction A) := by
  let := traceChartedSpace A
  let := pieceFintype
  have hs := (boundaryPartition A).contMDiff_finsum_smul (n := (⊤ : ℕ∞))
    (g := extendedPieceLevel A) (fun i p hp ↦
      contMDiffAt_extendedPieceLevel A i ⟨p, boundaryPartition_subordinate A i hp⟩)
  have he : boundaryDefiningFunction A =
      (fun p ↦ ∑ᶠ i, boundaryPartition A i p • extendedPieceLevel A i p) := by
    funext p
    rw [finsum_eq_sum_of_fintype]
    rfl
  rw [he]
  exact hs

theorem boundaryDefiningFunction_nonneg (p : ambientSet A) :
    0 ≤ boundaryDefiningFunction A p := by
  let := pieceFintype
  exact Finset.sum_nonneg (fun i _ ↦ weightedPieceLevel_nonneg A i p)

theorem boundaryDefiningFunction_zero_iff (p : ambientSet A) : letI := traceChartedSpace A;
    boundaryDefiningFunction A p = 0 ↔
      (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p := by
  let := traceChartedSpace A
  let := pieceFintype
  constructor
  · intro hz
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset Piece)) ↦ weightedPieceLevel_nonneg A i p)).mp hz
    obtain ⟨i, hi⟩ := (boundaryPartition A).exists_pos_of_mem (mem_univ p)
    have hp : p ∈ pieceDomain A i := boundaryPartition_subordinate A i
      (subset_tsupport (boundaryPartition A i) (ne_of_gt hi))
    have he : extendedPieceLevel A i p = 0 :=
      (mul_eq_zero.mp (hall i (Finset.mem_univ i))).resolve_left hi.ne'
    exact (pieceLevel_zero_iff A i ⟨p, hp⟩).mp
      ((extendedPieceLevel_on_piece A i ⟨p, hp⟩).symm.trans he)
  · intro hp
    change ∑ i, weightedPieceLevel A i p = 0
    apply Finset.sum_eq_zero
    intro i _
    change boundaryPartition A i p * extendedPieceLevel A i p = 0
    rw [extendedPieceLevel_zero_boundary A i ⟨p, hp⟩, mul_zero]

theorem boundaryDefiningFunction_pos_iff (p : ambientSet A) : letI := traceChartedSpace A;
    0 < boundaryDefiningFunction A p ↔
      ¬(ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p := by
  let := traceChartedSpace A
  rw [← boundaryDefiningFunction_zero_iff]
  exact lt_iff_le_and_ne.trans
    (and_iff_right (boundaryDefiningFunction_nonneg A p)) |>.trans ne_comm

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
