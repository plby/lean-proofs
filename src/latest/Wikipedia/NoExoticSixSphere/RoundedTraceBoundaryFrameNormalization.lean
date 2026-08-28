import Wikipedia.NoExoticSixSphere.RoundedTraceSignedBoundaryFrame
import Mathlib.Topology.Homotopy.Basic

/-!
# A genuine endpoint frame homotopy retaining the outward signs

Interpolate the nonzero last-column scale to the signed unit scale. Each
end keeps its strict sign throughout, so every stage spans the full actual
normal space. The final frame is norm preserving, with the original-end
last-coordinate reflection retained by `boundaryUnitFrame_top`.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def boundaryFrameScale (t : ℝ) (p : Boundary A) : ℝ :=
  (1 - t) * boundaryVerticalScale A p + t * boundaryUnitScale A p

theorem contMDiff_boundaryFrameScale : letI := boundaryChartedSpace A;
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 6)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × Boundary A ↦ boundaryFrameScale A q.1 q.2) := by
  let := boundaryChartedSpace A
  exact ((contMDiff_const.sub contMDiff_fst).mul
    ((contMDiff_boundaryVerticalScale A).comp contMDiff_snd)).add
      (contMDiff_fst.mul ((contMDiff_boundaryUnitScale A).comp contMDiff_snd))

theorem boundaryFrameScale_pos_other (t : I) (p : Boundary A) (hp : p.val ∈ otherEnd A) :
    0 < boundaryFrameScale A t p := by
  have hσ : 0 < boundaryUnitScale A p := by rw [boundaryUnitScale_other A p hp]; norm_num
  exact (convex_Ioi (0 : ℝ)) (boundaryVerticalScale_pos_other A p hp) hσ
    (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

theorem boundaryFrameScale_neg_top (t : I) (p : Boundary A) (hp : p.val ∈ topEnd A) :
    boundaryFrameScale A t p < 0 := by
  have hσ : boundaryUnitScale A p < 0 := by rw [boundaryUnitScale_top A p hp]; norm_num
  exact (convex_Iio (0 : ℝ)) (boundaryVerticalScale_neg_top A p hp) hσ
    (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

theorem boundaryFrameScale_ne_zero (t : I) (p : Boundary A) : boundaryFrameScale A t p ≠ 0 := by
  rcases (boundary_iff_mem_ends A p.val).mp p.property with hp | hp
  · exact ne_of_gt (boundaryFrameScale_pos_other A t p hp)
  · exact ne_of_lt (boundaryFrameScale_neg_top A t p hp)

def boundaryFrameFamily (t : ℝ) (p : Boundary A) :
    TimeGraphFrameSpace (e := e) →L[ℝ] Vector (e.ambientDimension + 6) :=
  OrthogonalUnitExtension.operator (traceNormalFrame A p.val)
    (boundaryFrameScale A t p • outwardNormal A p)

theorem contMDiff_boundaryFrameFamily : letI := boundaryChartedSpace A;
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 6)) 𝓘(ℝ, TimeGraphFrameSpace (e := e) →L[ℝ]
      Vector (e.ambientDimension + 6)) ∞
        (fun q : ℝ × Boundary A ↦ boundaryFrameFamily A q.1 q.2) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  have hB := (contMDiff_traceNormalFrame A).comp (contMDiff_boundaryInclusion A)
  exact OrthogonalUnitExtension.contMDiff_operator (hB.comp contMDiff_snd)
    ((contMDiff_boundaryFrameScale A).smul ((contMDiff_outwardNormal A).comp contMDiff_snd))

theorem boundaryFrameFamily_zero (p : Boundary A) :
    boundaryFrameFamily A 0 p = boundaryVerticalFrame A p := by
  rw [boundaryFrameFamily, boundaryFrameScale, sub_zero, one_mul, zero_mul, add_zero,
    boundaryVerticalFrame_eq_operator]

theorem boundaryFrameFamily_one (p : Boundary A) :
    boundaryFrameFamily A 1 p = boundaryUnitFrame A p := by
  rw [boundaryFrameFamily, boundaryFrameScale, sub_self, zero_mul, one_mul, zero_add]
  rfl

theorem boundaryFrameFamily_range (t : I) (p : Boundary A) :
    (boundaryFrameFamily A t p).range = (boundaryAmbientDerivative A p).rangeᗮ := by
  rw [boundaryFrameFamily,
    OrthogonalUnitExtension.range_operator_smul _ _ (boundaryFrameScale_ne_zero A t p),
    boundaryAppendedFrame_range]

theorem injective_boundaryFrameFamily (t : I) (p : Boundary A) :
    Injective (boundaryFrameFamily A t p) :=
  OrthogonalUnitExtension.injective_operator_smul _ _ (boundaryFrameScale_ne_zero A t p)
    (injective_boundaryAppendedFrame A p)

def boundaryVerticalFrameMap :
    C(Boundary A, TimeGraphFrameSpace (e := e) →L[ℝ] Vector (e.ambientDimension + 6)) :=
  ⟨boundaryVerticalFrame A, by
    let := boundaryChartedSpace A
    exact (contMDiff_boundaryVerticalFrame A).continuous⟩

def boundaryUnitFrameMap :
    C(Boundary A, TimeGraphFrameSpace (e := e) →L[ℝ] Vector (e.ambientDimension + 6)) :=
  ⟨boundaryUnitFrame A, by
    let := boundaryChartedSpace A
    exact (contMDiff_boundaryUnitFrame A).continuous⟩

def boundaryFrameFamilyMap :
    C(ℝ × Boundary A, TimeGraphFrameSpace (e := e) →L[ℝ] Vector (e.ambientDimension + 6)) :=
  ⟨fun q ↦ boundaryFrameFamily A q.1 q.2, by
    let := boundaryChartedSpace A
    exact (contMDiff_boundaryFrameFamily A).continuous⟩

def boundaryFrameHomotopy : (boundaryVerticalFrameMap A).Homotopy (boundaryUnitFrameMap A) where
  toContinuousMap := (boundaryFrameFamilyMap A).comp
    ((⟨fun t : I ↦ (t : ℝ), continuous_subtype_val⟩ : C(I, ℝ)).prodMap (ContinuousMap.id _))
  map_zero_left p := boundaryFrameFamily_zero A p
  map_one_left p := boundaryFrameFamily_one A p

theorem boundaryFrameHomotopy_range (t : I) (p : Boundary A) :
    (boundaryFrameHomotopy A (t, p)).range = (boundaryAmbientDerivative A p).rangeᗮ :=
  boundaryFrameFamily_range A t p

theorem injective_boundaryFrameHomotopy (t : I) (p : Boundary A) :
    Injective (boundaryFrameHomotopy A (t, p)) := injective_boundaryFrameFamily A t p

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
