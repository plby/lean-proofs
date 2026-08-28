import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyCap
import Wikipedia.SmoothSixDPoincare.SmoothClosedFaceOpenEmbedding
import Wikipedia.SmoothSixDPoincare.FramedSurgeryRetainedBodyFace

/-!
# Lift the same whole face from the remaining boundary of a disk cap

The native open-submanifold inclusion preserves all face parameters and
its full smooth chart. The lifted face avoids the capped sphere, and its
whole-body face map factors exactly through the original cap quotient.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

open FramedSurgery PuncturedHandle

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} (U : SmoothBoundaryBody J)
  {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  (j : C(UnitSphere N, U.boundary)) (hj : IsClosedEmbedding j) (hopen : IsOpen (range j))
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F (U.cap j hj hopen).boundary)
  (x₀ : U.capBoundary j hj)

def liftCapFace : SmoothClosedFace (𝓡 m) J (UnitSphere E) F U.boundary := by
  let _ : Nonempty (U.capBoundary j hj) := ⟨x₀⟩
  exact A.postcomposeOpen (PartialChart.openInclusion (I := J) (U.capBoundary j hj))
    (PartialChart.openInclusion_source (I := J) (U.capBoundary j hj))

theorem liftCapFace_map (z : UnitSphere E × MorseHandle.UnitDisk F) :
    (U.liftCapFace j hj hopen A x₀).map z = (A.map z).val := rfl

theorem liftCapFace_disjoint : Disjoint (range (U.liftCapFace j hj hopen A x₀).map) (range j) := by
  apply disjoint_left.mpr
  rintro y ⟨z, rfl⟩ hy
  exact (A.map z).property hy

theorem liftCapFace_bodyFaceMap :
    bodyFaceMap A (U.cap j hj hopen).inclusion =
      (FaceAttachment.oldMap (U.capFaceMap j)).comp
        (bodyFaceMap (U.liftCapFace j hj hopen A x₀) U.inclusion) := rfl

theorem capSphere_avoids_liftedFace (v : UnitSphere N) :
    j v ∉ range (U.liftCapFace j hj hopen A x₀).map := by
  intro hv
  exact disjoint_left.mp (U.liftCapFace_disjoint j hj hopen A x₀) hv ⟨v, rfl⟩

theorem capSphere_avoids_liftedInterior (v : UnitSphere N) :
    j v ∉ faceInterior (U.liftCapFace j hj hopen A x₀) :=
  fun hv => U.capSphere_avoids_liftedFace j hj hopen A x₀ v (faceInterior_subset_range hv)

theorem capSphere_mem_liftedOldPatch (v : UnitSphere N) :
    j v ∈ oldPatch (U.liftCapFace j hj hopen A x₀) := by
  rintro ⟨u, hu⟩
  exact U.capSphere_avoids_liftedFace j hj hopen A x₀ v ⟨(u, ⟨0, by simp⟩), hu⟩

def retainedCapOldMap : C(UnitSphere N, oldPatch (U.liftCapFace j hj hopen A x₀)) :=
  ⟨fun v => ⟨j v, U.capSphere_mem_liftedOldPatch j hj hopen A x₀ v⟩,
    j.continuous.subtype_mk _⟩

theorem retainedCapOldMap_point (v : UnitSphere N) :
    (U.retainedCapOldMap j hj hopen A x₀ v).val = j v := rfl

theorem retainedCapOldMap_range : range (U.retainedCapOldMap j hj hopen A x₀) =
    (Subtype.val : oldPatch (U.liftCapFace j hj hopen A x₀) → U.boundary) ⁻¹' range j := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩
  · rintro ⟨v, hv⟩; exact ⟨v, Subtype.ext hv⟩

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
