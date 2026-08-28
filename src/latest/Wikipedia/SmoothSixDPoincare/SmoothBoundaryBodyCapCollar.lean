import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyCap
import Wikipedia.SmoothSixDPoincare.NativeInwardBoundaryCollar
import Wikipedia.SmoothSixDPoincare.InwardCollarOpenPart
import Wikipedia.SmoothSixDPoincare.FaceAttachmentOldOpen

/-!
# A cap preserves the collar of the remaining boundary

The old collar over the complementary boundary component is disjoint from
the entire attaching sphere. Its inner image remains open in the actual
disk-attachment quotient, so no extension across the cap disk is needed.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} (U : SmoothBoundaryBody J)
  {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  (j : C(PuncturedHandle.UnitSphere N, U.boundary)) (hj : IsClosedEmbedding j)
  (hopen : IsOpen (range j)) (C : InwardBoundaryCollar U.inclusion)

def capCollarOldMap : C((U.cap j hj hopen).boundary × unitInterval, U.body) :=
  ⟨fun q => C.map (q.1.val, q.2),
    C.map.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩

def capCollarMap : C((U.cap j hj hopen).boundary × unitInterval, (U.cap j hj hopen).body) :=
  (FaceAttachment.oldMap (U.capFaceMap j)).comp (U.capCollarOldMap j hj hopen C)

theorem capCollarMap_injective : Injective (U.capCollarMap j hj hopen C) := by
  intro q r h
  have hOld := (FaceAttachment.oldMap_eq_oldMap (U.capFaceMap j)
    (U.capFaceMap_injective j hj) _ _).mp h
  have hc := C.closedEmbedding.injective hOld
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hc))
    (congrArg (fun p : U.boundary × unitInterval => p.2) hc)

theorem capCollarOldMap_avoids (q : (U.cap j hj hopen).boundary × unitInterval) :
    U.capCollarOldMap j hj hopen C q ∉ range (U.capFaceMap j) := by
  rintro ⟨v, hv⟩
  have he : C.map (j (DiskCap.boundaryCoordinates N v), 0) = C.map (q.1.val, q.2) :=
    (C.zero (j (DiskCap.boundaryCoordinates N v))).trans hv
  exact q.1.property ⟨DiskCap.boundaryCoordinates N v,
    congrArg Prod.fst (C.closedEmbedding.injective he)⟩

theorem capCollarOldMap_inner_image :
    U.capCollarOldMap j hj hopen C ''
        {q : (U.cap j hj hopen).boundary × unitInterval | q.2 < 1} =
      C.map '' {q : U.boundary × unitInterval | q.1 ∈ U.capBoundary j hj ∧ q.2 < 1} := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨(q.1.val, q.2), ⟨q.1.property, hq⟩, rfl⟩
  · rintro ⟨q, ⟨hV, ht⟩, rfl⟩
    exact ⟨(⟨q.1, hV⟩, q.2), ht, rfl⟩

theorem capCollarMap_inner_open :
    IsOpen (U.capCollarMap j hj hopen C ''
      {q : (U.cap j hj hopen).boundary × unitInterval | q.2 < 1}) := by
  let s := U.capCollarOldMap j hj hopen C ''
    {q : (U.cap j hj hopen).boundary × unitInterval | q.2 < 1}
  have hs : IsOpen s := by
    change IsOpen (U.capCollarOldMap j hj hopen C ''
      {q : (U.cap j hj hopen).boundary × unitInterval | q.2 < 1})
    exact (U.capCollarOldMap_inner_image j hj hopen C).symm ▸
      C.inner_image_open (U.capBoundary j hj)
  have hd : Disjoint s (range (U.capFaceMap j)) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨q, _, rfl⟩ hy
    exact U.capCollarOldMap_avoids j hj hopen C q hy
  have heq : U.capCollarMap j hj hopen C ''
      {q : (U.cap j hj hopen).boundary × unitInterval | q.2 < 1} =
        FaceAttachment.oldMap (U.capFaceMap j) '' s := by
    rw [show s = U.capCollarOldMap j hj hopen C ''
      {q : (U.cap j hj hopen).boundary × unitInterval | q.2 < 1} from rfl, Set.image_image]
    rfl
  exact heq.symm ▸ FaceAttachment.old_image_open (U.capFaceMap j)
    (U.capFaceMap_injective j hj) s hs hd

def capInwardCollar : InwardBoundaryCollar (U.cap j hj hopen).inclusion where
  map := U.capCollarMap j hj hopen C
  closedEmbedding := (U.capCollarMap j hj hopen C).continuous.isClosedEmbedding
    (U.capCollarMap_injective j hj hopen C)
  zero x := congrArg (FaceAttachment.oldMap (U.capFaceMap j)) (C.zero x.val)
  inner_open := U.capCollarMap_inner_open j hj hopen C

theorem cap_hasInwardCollar (hU : U.HasInwardCollar) : (U.cap j hj hopen).HasInwardCollar := by
  obtain ⟨C⟩ := hU
  exact ⟨U.capInwardCollar j hj hopen C⟩

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
