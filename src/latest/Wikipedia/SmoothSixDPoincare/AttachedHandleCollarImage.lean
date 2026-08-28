import Wikipedia.SmoothSixDPoincare.AttachedHandleCollarEmbedding
import Wikipedia.SmoothSixDPoincare.HandleCollarCoordinateImage

/-!
# The assembled collar is an actual open boundary neighborhood

Its open-ended image is exactly the strict depth sublevel in the original
attachment quotient. Every shallow old-body point and every shallow whole-
handle point has constructed collar parameters. Together with injectivity,
this supplies a genuine inward collar of the actual surgery boundary.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

variable {E F G H X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F X)
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  (i : C(X, Y)) (C : InwardBoundaryCollar i) (hi : IsClosedEmbedding i)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

omit [T2Space Y] [CompactSpace Y] in
theorem collarMap_inner_of_shallow_model (z : WholeHandle E F)
    (hz : attachedCollarDepth A i C
      (CollaredHandleEmbedding.parametrization A.map i C hi.injective A.closedEmbedding.injective z)
        < 1 / 2) :
    CollaredHandleEmbedding.parametrization A.map i C hi.injective A.closedEmbedding.injective z ∈
      collarMap A i C hi n '' {q : Boundary A n × unitInterval | q.2 < 1} := by
  rw [attachedCollarDepth_parametrization] at hz
  have hw : HandleCollarDepth.depth (2 * ‖z.1.val‖ - 1) (1 - ‖z.2.val‖) < 1 / 2 :=
    (min_lt_iff.mp hz).resolve_left (by norm_num)
  obtain ⟨q, hq, hval⟩ : z ∈ HandleCollarCoordinates.coordinates ''
      {q : ClosedNewFace E F × unitInterval | q.2 < 1} := by
    rw [HandleCollarCoordinates.coordinates_inner_image]
    exact hw
  refine ⟨(closedNewMap A n q.1, q.2), hq, ?_⟩
  rw [collarMap_new]
  exact congrArg
    (CollaredHandleEmbedding.parametrization A.map i C hi.injective
      A.closedEmbedding.injective) hval

omit [T2Space Y] [CompactSpace Y] in
theorem collarMap_inner_image :
    collarMap A i C hi n '' {q : Boundary A n × unitInterval | q.2 < 1} =
      {y : AttachedBody A i | attachedCollarDepth A i C y < 1 / 2} := by
  ext y
  constructor
  · rintro ⟨⟨z, t⟩, ht, rfl⟩
    change attachedCollarDepth A i C (collarMap A i C hi n (z, t)) < 1 / 2
    rw [collarMap_depth]
    have ht' : (t : ℝ) < 1 := ht
    unfold HandleCollarCoordinates.time
    linarith
  · change attachedCollarDepth A i C y < 1 / 2 →
      y ∈ collarMap A i C hi n '' {q : Boundary A n × unitInterval | q.2 < 1}
    refine FaceAttachment.induction_on (bodyFaceMap A i) y
      (P := fun z => attachedCollarDepth A i C z < 1 / 2 →
        z ∈ collarMap A i C hi n '' {q : Boundary A n × unitInterval | q.2 < 1}) ?_ ?_
    · intro y hy
      have hinner : y ∈ C.innerRegion :=
        C.bodyDepth_lt_one_mem A.normalDeficit (fun x => (A.normalDeficit_bounds x).1)
          (show oldCollarDepth A i C y < 1 from hy.trans (by norm_num))
      obtain ⟨⟨x, t⟩, _, rfl⟩ := hinner
      by_cases hx : x ∈ range A.map
      · obtain ⟨a, rfl⟩ := hx
        let z : WholeHandle E F := CollaredDiskAttachment.oldMap (a.1, t, a.2)
        have hmodel : CollaredHandleEmbedding.parametrization A.map i C hi.injective
            A.closedEmbedding.injective z =
            FaceAttachment.oldMap (bodyFaceMap A i) (C.map (A.map a, t)) :=
          CollaredHandleEmbedding.parametrization_old A.map i C hi.injective
            A.closedEmbedding.injective (a.1, t, a.2)
        have hm := collarMap_inner_of_shallow_model A i C hi n z (by rw [hmodel]; exact hy)
        exact hmodel ▸ hm
      · have hxI : x ∉ A.interiorImage := fun h => hx (A.interiorImage_subset_range h)
        have ht : (t : ℝ) < 1 / 2 := by
          rw [← attachedCollarDepth_exterior A i C x hxI t]
          exact hy
        let s : unitInterval := ⟨2 * (t : ℝ), by constructor <;> linarith [t.property.1]⟩
        have hs : s < 1 := by change 2 * (t : ℝ) < 1; linarith
        let r : Exterior A := ⟨x, by
          simpa only [A.interiorImage_eq_chart, faceInterior] using hxI⟩
        have hts : HandleCollarCoordinates.oldTime s = t := by
          apply Subtype.ext
          dsimp [HandleCollarCoordinates.oldTime, HandleCollarCoordinates.time, s]
          ring
        refine ⟨(exteriorNewMap A n r, s), hs, ?_⟩
        rw [collarMap_exterior, hts]
    · intro k hk
      let z : WholeHandle E F := CollaredDiskAttachment.newMap k
      have hmodel : CollaredHandleEmbedding.parametrization A.map i C hi.injective
          A.closedEmbedding.injective z = FaceAttachment.handleMap (bodyFaceMap A i) k :=
        CollaredHandleEmbedding.parametrization_new A.map i C hi.injective
          A.closedEmbedding.injective k
      have hm := collarMap_inner_of_shallow_model A i C hi n z (by rw [hmodel]; exact hk)
      exact hmodel ▸ hm

omit [T2Space Y] [CompactSpace Y] in
theorem collarMap_inner_open :
    IsOpen (collarMap A i C hi n '' {q : Boundary A n × unitInterval | q.2 < 1}) := by
  rw [collarMap_inner_image]
  exact isOpen_lt (attachedCollarDepth A i C).continuous continuous_const

def inwardCollar : InwardBoundaryCollar (boundaryBodyMap A i n hi) where
  map := collarMap A i C hi n
  closedEmbedding := collarMap_isClosedEmbedding A i C hi n
  zero := collarMap_zero A i C hi n
  inner_open := collarMap_inner_open A i C hi n

end Wikipedia.SmoothSixDPoincare.FramedSurgery
