import Wikipedia.NoExoticSixSphere.RoundedTraceTimeGraphFrame

/-!
# The smooth outward slope of the actual bordism time

The slope is evaluated on the intrinsic outward tangent section, so its
smoothness follows from the bundled tangent map. At the native boundary,
the entire time differential is this slope times the ambient unit outward
covector. This fixes the two-plane needed for the end-frame comparison.
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

def boundaryTimeSlope (p : Boundary A) : ℝ :=
  bordismTimeDifferential A p.val (outwardTraceVector A p)

theorem contMDiff_boundaryTimeSlope : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) 𝓘(ℝ, ℝ) ∞ (boundaryTimeSlope A) := by
  let := traceChartedSpace A
  let := trace_isManifold A
  let := boundaryChartedSpace A
  have ht := (contMDiff_bordismTime A).contMDiff_tangentMap (m := ∞) (by simp)
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp
    (ht.comp (contMDiff_outwardTangentSection A))

theorem boundaryTimeSlope_ne_zero (p : Boundary A) : boundaryTimeSlope A p ≠ 0 := by
  rcases (boundary_iff_mem_ends A p.val).mp p.property with hp | hp
  · exact (bordismTimeDifferential_outward_other A p hp).ne
  · exact (bordismTimeDifferential_outward_top A p hp).ne'

theorem continuous_boundaryTimeSlope : Continuous (boundaryTimeSlope A) := by
  let := boundaryChartedSpace A
  exact (contMDiff_boundaryTimeSlope A).continuous

theorem inner_outward_traceDerivative_kernel (p : Boundary A) (v : ℝ × Vector 6)
    (hv : v ∈ (bordismTimeDifferential A p.val).ker) :
    inner ℝ (outwardNormal A p) (traceAmbientDerivative A p.val v) = 0 := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  rw [← range_boundaryTraceDifferential_time] at hv
  obtain ⟨w, hw⟩ := hv
  change boundaryTraceDifferential A p w = v at hw
  have hd := congrArg (fun D : Vector 6 →L[ℝ] Vector (e.ambientDimension + 6) ↦ D w)
    (boundaryAmbientDerivative_eq A p)
  change boundaryAmbientDerivative A p w =
    traceAmbientDerivative A p.val (boundaryTraceDifferential A p w) at hd
  rw [hw] at hd
  rw [← hd]
  exact (real_inner_comm _ _).trans
    ((boundaryAmbientDerivative A p).range.inner_right_of_mem_orthogonal ⟨w, rfl⟩
      (outwardNormal_mem_boundaryNormal A p))

theorem bordismTimeDifferential_outward_covector (p : Boundary A) (v : ℝ × Vector 6) :
    bordismTimeDifferential A p.val v =
      boundaryTimeSlope A p * inner ℝ (outwardNormal A p) (traceAmbientDerivative A p.val v) := by
  let l := bordismTimeDifferential A p.val
  let u := outwardTraceVector A p
  let c := l v / boundaryTimeSlope A p
  have hn := boundaryTimeSlope_ne_zero A p
  have hk : v - c • u ∈ l.ker := by
    change l (v - c • u) = 0
    rw [map_sub, map_smul]
    change l v - (l v / boundaryTimeSlope A p) * boundaryTimeSlope A p = 0
    rw [div_mul_cancel₀ _ hn, sub_self]
  have he := inner_outward_traceDerivative_kernel A p (v - c • u) hk
  rw [map_sub, map_smul, inner_sub_right, real_inner_smul_right,
    traceDerivative_outwardTraceVector, real_inner_self_eq_norm_sq, norm_outwardNormal,
    one_pow, mul_one] at he
  have hc : inner ℝ (outwardNormal A p) (traceAmbientDerivative A p.val v) = c :=
    sub_eq_zero.mp he
  rw [hc]
  change l v = boundaryTimeSlope A p * (l v / boundaryTimeSlope A p)
  exact (mul_div_cancel₀ _ hn).symm

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
