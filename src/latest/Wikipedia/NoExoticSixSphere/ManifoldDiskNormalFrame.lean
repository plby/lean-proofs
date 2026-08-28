import Wikipedia.NoExoticSixSphere.ManifoldSphereDisk

/-!
# The original manifold's normal frame along a disk in the manifold

Smoothness and normality are inherited from the actual embedding and the
given normal frame. The disk's native derivative is used without replacing
the tangent or normal spaces by independent plane data.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (h : Vector 4 → M) (x : Vector 4)
  (hs : ContMDiffAt (𝓡 4) (𝓡 6) ∞ h x)

include hs in
theorem contDiffAt_comp_disk : ContDiffAt ℝ ∞ (e.toFun ∘ h) x :=
  (e.smooth.contMDiffAt.comp x hs).contDiffAt

include hs in
theorem injective_fderiv_comp_disk (hi : Injective (mfderiv (𝓡 4) (𝓡 6) h x)) :
    Injective (fderiv ℝ (e.toFun ∘ h) x) := by
  rw [← mfderiv_eq_fderiv, mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp))]
  exact (e.injective_mfderiv (h x)).comp hi

variable (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

include hs in
theorem normalFrameOnDisk_contDiffAt :
    ContDiffAt ℝ ∞ (fun y : Vector 4 ↦ (a.orthonormal (h y)).val) x :=
  (a.contMDiff_orthonormal.contMDiffAt.comp x hs).contDiffAt

include hs in
theorem normalFrameOnDisk_normal :
    (a.orthonormal (h x)).val.range ≤ (fderiv ℝ (e.toFun ∘ h) x).rangeᗮ := by
  rw [a.orthonormal_range, e.range_normalProjection]
  apply Submodule.orthogonal_le
  rw [← mfderiv_eq_fderiv, mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp))]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

end NoExoticSixSphere.EuclideanEmbedding
