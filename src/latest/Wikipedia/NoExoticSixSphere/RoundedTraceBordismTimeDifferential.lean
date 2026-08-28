import Wikipedia.NoExoticSixSphere.RoundedTraceBordismTime

/-!
# Regular end levels and coorientation of the bordism time

The time differential is the boundary-equation differential at the surgery
end and its negative at the original end. These are equalities of actual
manifold differentials, obtained by differentiating the defining identity.
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

theorem endCutoff_differential_boundary (p : Boundary A) : letI := traceChartedSpace A;
    mvfderiv (ProductHalfSpace.model (Vector 6)) (endCutoff A) p.val = 0 := by
  let := traceChartedSpace A
  rcases (boundary_iff_mem_ends A p.val).mp p.property with hp | hp
  · have he : (endCutoff A : ambientSet A → ℝ) =ᶠ[𝓝 p.val] (fun _ ↦ 0) :=
      (endCutoff_eventually_zero A).filter_mono (nhds_le_nhdsSet hp)
    have hd := he.mfderiv_eq (I := ProductHalfSpace.model (Vector 6)) (I' := 𝓘(ℝ, ℝ))
    rw [mfderiv_const] at hd
    exact hd
  · have he : (endCutoff A : ambientSet A → ℝ) =ᶠ[𝓝 p.val] (fun _ ↦ 1) :=
      (endCutoff_eventually_one A).filter_mono (nhds_le_nhdsSet hp)
    have hd := he.mfderiv_eq (I := ProductHalfSpace.model (Vector 6)) (I' := 𝓘(ℝ, ℝ))
    rw [mfderiv_const] at hd
    exact hd

theorem bordismTime_boundary (p : Boundary A) : letI := traceChartedSpace A;
    bordismTime A p.val = endCutoff A p.val := by
  let := traceChartedSpace A
  have hz := (boundaryDefiningFunction_zero_iff A p.val).mpr p.property
  simp only [bordismTime, hz, add_zero, mul_zero, div_one]

def bordismTimeDifferential (p : ambientSet A) : (ℝ × Vector 6) →L[ℝ] ℝ :=
  letI := traceChartedSpace A
  mvfderiv (ProductHalfSpace.model (Vector 6)) (bordismTime A) p

theorem bordismTimeDifferential_boundary (p : Boundary A) : letI := traceChartedSpace A;
    bordismTimeDifferential A p.val =
      (1 - 2 * endCutoff A p.val) • boundaryDefiningDifferential A p.val := by
  let := traceChartedSpace A
  have hφ := (contMDiff_boundaryDefiningFunction A).mdifferentiableAt (x := p.val) (by simp)
  have hχ := (endCutoff A).contMDiff.mdifferentiableAt (x := p.val) (by simp)
  have ht := (contMDiff_bordismTime A).mdifferentiableAt (x := p.val) (by simp)
  have hc : MDifferentiableAt (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, ℝ)
      (fun _ : ambientSet A ↦ (2 : ℝ)) p.val := mdifferentiableAt_const
  have hden : MDifferentiableAt (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, ℝ)
      (fun q ↦ 1 + 2 * boundaryDefiningFunction A q) p.val :=
    mdifferentiableAt_const.add (hc.mul hφ)
  have hdenD : mvfderiv (ProductHalfSpace.model (Vector 6))
      (fun q ↦ 1 + 2 * boundaryDefiningFunction A q) p.val =
      (2 : ℝ) • boundaryDefiningDifferential A p.val := by
    change mvfderiv (ProductHalfSpace.model (Vector 6))
      (fun q ↦ 1 + 2 * boundaryDefiningFunction A q) p.val =
      (2 : ℝ) • mvfderiv (ProductHalfSpace.model (Vector 6)) (boundaryDefiningFunction A) p.val
    have hd := mvfderiv_add (mdifferentiableAt_const (c := (1 : ℝ))) (hc.mul hφ)
    rw [mvfderiv_const, mvfderiv_mul hc hφ, mvfderiv_const] at hd
    simp only [zero_add, smul_zero, add_zero] at hd
    change mvfderiv (ProductHalfSpace.model (Vector 6))
      (fun q ↦ 1 + 2 * boundaryDefiningFunction A q) p.val =
      (2 : ℝ) • mvfderiv (ProductHalfSpace.model (Vector 6))
        (boundaryDefiningFunction A) p.val at hd
    exact hd
  have hnumD : mvfderiv (ProductHalfSpace.model (Vector 6))
      (fun q ↦ endCutoff A q + boundaryDefiningFunction A q) p.val =
      boundaryDefiningDifferential A p.val := by
    rw [mvfderiv_fun_add hχ hφ, endCutoff_differential_boundary, zero_add]
    rfl
  have he : (fun q ↦ bordismTime A q * (1 + 2 * boundaryDefiningFunction A q)) =
      (fun q ↦ endCutoff A q + boundaryDefiningFunction A q) := by
    funext q
    exact div_mul_cancel₀ _ (bordismTime_denominator_pos A q).ne'
  have hd := congrArg
    (fun g : ambientSet A → ℝ ↦ mvfderiv (ProductHalfSpace.model (Vector 6)) g p.val) he
  rw [mvfderiv_fun_mul ht hden, hdenD, hnumD] at hd
  have hz := (boundaryDefiningFunction_zero_iff A p.val).mpr p.property
  rw [hz, mul_zero, add_zero, one_smul, bordismTime_boundary] at hd
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun D : (ℝ × Vector 6) →L[ℝ] ℝ ↦ D v) hd
  change endCutoff A p.val * (2 * boundaryDefiningDifferential A p.val v) +
    bordismTimeDifferential A p.val v = boundaryDefiningDifferential A p.val v at hv
  change bordismTimeDifferential A p.val v =
    (1 - 2 * endCutoff A p.val) * boundaryDefiningDifferential A p.val v
  linarith

theorem bordismTimeDifferential_otherEnd (p : Boundary A) (hp : p.val ∈ otherEnd A) :
    bordismTimeDifferential A p.val = boundaryDefiningDifferential A p.val := by
  let := traceChartedSpace A
  rw [bordismTimeDifferential_boundary, endCutoff_zero A hp]
  simp only [mul_zero, sub_zero, one_smul]

theorem bordismTimeDifferential_topEnd (p : Boundary A) (hp : p.val ∈ topEnd A) :
    bordismTimeDifferential A p.val = -boundaryDefiningDifferential A p.val := by
  let := traceChartedSpace A
  rw [bordismTimeDifferential_boundary, endCutoff_one A hp]
  norm_num

theorem bordismTimeDifferential_outward_other (p : Boundary A) (hp : p.val ∈ otherEnd A) :
    bordismTimeDifferential A p.val (outwardTraceVector A p) < 0 := by
  rw [bordismTimeDifferential_otherEnd A p hp]
  exact boundaryDefiningDifferential_outward A p

theorem bordismTimeDifferential_outward_top (p : Boundary A) (hp : p.val ∈ topEnd A) :
    0 < bordismTimeDifferential A p.val (outwardTraceVector A p) := by
  rw [bordismTimeDifferential_topEnd A p hp]
  exact neg_pos.mpr (boundaryDefiningDifferential_outward A p)

theorem bordismTimeDifferential_surjective (p : Boundary A) :
    Surjective (bordismTimeDifferential A p.val) := by
  rcases (boundary_iff_mem_ends A p.val).mp p.property with hp | hp
  · rw [bordismTimeDifferential_otherEnd A p hp]
    exact boundaryDefiningDifferential_surjective A p
  · rw [bordismTimeDifferential_topEnd A p hp]
    intro y
    obtain ⟨v, hv⟩ := boundaryDefiningDifferential_surjective A p (-y)
    exact ⟨v, by change -(boundaryDefiningDifferential A p.val v) = y; rw [hv, neg_neg]⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
