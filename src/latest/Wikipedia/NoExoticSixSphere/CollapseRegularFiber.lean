import Wikipedia.NoExoticSixSphere.SmoothFramedCollapse

/-!
# The embedded manifold as a regular finite-coordinate fiber

The local zero fiber is exactly the given embedded manifold. Its tangent
image is precisely the kernel of the local collapse differential, and the
specified normal frame is identified by that differential.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

theorem coordinates_zero_iff {y : EuclideanSpace ℝ (Fin e.ambientDimension)}
    (hy : y ∈ d.neighborhood) : d.coordinates y = 0 ↔ ∃ x, e.toFun x = y := by
  have h := d.zero_fiber (y : OnePoint _)
  rw [d.local_formula y hy, OnePoint.coe_injective.eq_iff] at h
  simpa only [OnePoint.coe_injective.eq_iff] using h

theorem coordinates_zero (x : M) : d.coordinates (e.toFun x) = 0 :=
  (d.coordinates_zero_iff (d.range_subset ⟨x, rfl⟩)).mpr ⟨x, rfl⟩

theorem contDiffAt_coordinates {y : EuclideanSpace ℝ (Fin e.ambientDimension)}
    (hy : y ∈ d.neighborhood) : ContDiffAt ℝ ∞ d.coordinates y :=
  d.smooth_coordinates.contDiffAt (d.open_neighborhood.mem_nhds hy)

theorem differential_comp_tangent (x : M) :
    (fderiv ℝ d.coordinates (e.toFun x)).comp (mvfderiv (𝓡 n) e.toFun x) = 0 := by
  have hd := (d.contDiffAt_coordinates (d.range_subset ⟨x, rfl⟩)).differentiableAt (by simp)
  have hc : d.coordinates ∘ e.toFun = fun _ ↦ (0 : e.NormalModel) :=
    funext d.coordinates_zero
  have h := mfderiv_comp x hd.mdifferentiableAt (e.smooth.mdifferentiable (by simp) x)
  rw [hc, mfderiv_const, mfderiv_eq_fderiv] at h
  exact h.symm

theorem tangentImage_le_kernel (x : M) :
    e.tangentImage x ≤ (fderiv ℝ d.coordinates (e.toFun x)).ker := by
  rintro v ⟨w, rfl⟩
  change (fderiv ℝ d.coordinates (e.toFun x)) (mvfderiv (𝓡 n) e.toFun x w) = 0
  exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] e.NormalModel ↦ L w)
    (d.differential_comp_tangent x)

theorem kernel_eq_tangentImage (x : M) :
    (fderiv ℝ d.coordinates (e.toFun x)).ker = e.tangentImage x := by
  let L := fderiv ℝ d.coordinates (e.toFun x)
  have hsurj : Function.Surjective L := d.surjective_differential _ (d.range_subset ⟨x, rfl⟩)
  have hdim := L.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hdim
  have hnormal : finrank ℝ e.NormalModel = e.ambientDimension - n :=
    finrank_euclideanSpace_fin
  have hambient : finrank ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) = e.ambientDimension :=
    finrank_euclideanSpace_fin
  rw [hnormal, hambient] at hdim
  have hle := e.dimension_le_ambient x
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq (d.tangentImage_le_kernel x)
  rw [e.finrank_tangentImage]
  change n = finrank ℝ L.ker
  omega

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
