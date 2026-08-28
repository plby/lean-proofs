import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyCapLift
import Wikipedia.SmoothSixDPoincare.OpenPartitionDiffeomorph
import Wikipedia.SmoothSixDPoincare.SmoothClosedFaceSum

/-! # The native boundary splits into the retained cap complement and the capped sphere image -/

noncomputable section

open Set Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

open FramedSurgery PuncturedHandle

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} (U : SmoothBoundaryBody J)
  {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  (j : C(UnitSphere N, U.boundary)) (hj : IsClosedEmbedding j) (hopen : IsOpen (range j))

def capSphereOpen : Opens U.boundary := ⟨range j, hopen⟩

def capSphereCoordinates : UnitSphere N ≃ₜ U.capSphereOpen j hopen := hj.toHomeomorph

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
include hj in
theorem capSphereOpen_compact : CompactSpace (U.capSphereOpen j hopen) :=
  isCompact_iff_compactSpace.mp hj.isClosed_range.isCompact

def capPartitionDiffeomorph : Diffeomorph J J
    ((U.cap j hj hopen).boundary ⊕ U.capSphereOpen j hopen) U.boundary ∞ :=
  OpenPartition.diffeomorph (U.capBoundary j hj) (U.capSphereOpen j hopen)
    disjoint_compl_left (compl_union_self _)

theorem capPartitionDiffeomorph_left (x : (U.cap j hj hopen).boundary) :
    U.capPartitionDiffeomorph j hj hopen (Sum.inl x) = x.val := rfl

theorem capPartitionDiffeomorph_right (y : U.capSphereOpen j hopen) :
    U.capPartitionDiffeomorph j hj hopen (Sum.inr y) = y.val := rfl

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F (U.cap j hj hopen).boundary)
  (x₀ : U.capBoundary j hj)

theorem liftCapFace_partition (z : UnitSphere E × MorseHandle.UnitDisk F) :
    U.capPartitionDiffeomorph j hj hopen
        ((A.sumLeft (Z := U.capSphereOpen j hopen) x₀).map z) =
      (U.liftCapFace j hj hopen A x₀).map z := rfl

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
