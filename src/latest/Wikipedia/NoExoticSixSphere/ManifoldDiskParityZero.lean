import Wikipedia.NoExoticSixSphere.ManifoldSphereParity
import Wikipedia.NoExoticSixSphere.ManifoldDiskNormalFrame
import Wikipedia.NoExoticSixSphere.FlattenedDiskFrame

/-!
# Zero sphere parity for a disk embedded in the original manifold

A smooth embedded immersive four-disk in the manifold supplies an explicit
normal-frame extension on a constructed compatible spanning disk. Thus the
disk-independent sphere parity is zero. An arbitrary nullhomotopy is not
assumed to be embedded or immersive.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereParity_zero_of_embedded_disk (f : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (h : Vector 4 → M) (hext : ∀ s : Sphere 3, h s.val = f s)
    (hs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContMDiffAt (𝓡 4) (𝓡 6) ∞ h x)
    (hhi : InjOn h (closedBall (0 : Vector 4) 1))
    (hhd : ∀ x ∈ closedBall (0 : Vector 4) 1,
      Injective (mfderiv (𝓡 4) (𝓡 6) h x)) : e.sphereParity a f hf hi hd = 0 := by
  let F : Vector 4 → Vector e.ambientDimension := e.toFun ∘ h
  have hF : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x :=
    fun x hx ↦ e.contDiffAt_comp_disk h x (hs x hx)
  have hFi : InjOn F (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy he
    exact hhi hx hy (e.closedEmbedding.injective he)
  have hFd : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ F x) :=
    fun x hx ↦ e.injective_fderiv_comp_disk h x (hs x hx) (hhd x hx)
  have hEF : ∀ s : Sphere 3, F s.val = (e.toFun ∘ f) s :=
    fun s ↦ congrArg e.toFun (hext s)
  let W : Vector 4 → Space e.ambientDimension (e.ambientDimension - 6) :=
    fun x ↦ a.orthonormal (h x)
  have hWs : ∀ x ∈ closedBall (0 : Vector 4) 1,
      ContDiffAt ℝ ∞ (fun y ↦ (W y).val) x :=
    fun x hx ↦ e.normalFrameOnDisk_contDiffAt h x (hs x hx) a
  have hWn : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (W x).val.range ≤ (fderiv ℝ F x).rangeᗮ :=
    fun x hx ↦ e.normalFrameOnDisk_normal h x (hs x hx) a
  have hWb : ∀ s : Sphere 3, W s.val = e.normalFrameOnSphere a f s := by
    intro s
    change a.orthonormal (h s.val) = a.orthonormal (f s)
    rw [hext]
  let D := FlattenedSpanningDisk.diskData F (pole 3) (e.toFun ∘ f) hEF hF hFi hFd
  rw [e.sphereParity_eq a f hf hi hd D]
  exact FlattenedSpanningDisk.parityOfDimension_zero_of_disk_frame
    (Nat.sub_add_cancel (e.dimension_le_ambient (f (pole 3)))).symm
    F (pole 3) (e.toFun ∘ f) hEF hF hFi hFd (e.smooth.comp hf)
    (e.normalFrameOnSphere a f) (e.contMDiff_normalFrameOnSphere a f hf)
    (e.normalFrameOnSphere_normal a f hf) W hWs hWn hWb

end NoExoticSixSphere.EuclideanEmbedding
