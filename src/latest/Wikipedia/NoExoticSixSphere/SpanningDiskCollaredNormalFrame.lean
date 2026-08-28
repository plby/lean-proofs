import Wikipedia.NoExoticSixSphere.StabilizedDiskRadialFrame
import Wikipedia.NoExoticSixSphere.SmoothDiskNormalCollarFrame

/-!
# A spanning disk's normal frame with exact radial collar values

Any smooth extension of the stabilized original boundary frame can be replaced
by one equal to that frame's radial extension on a whole inner annulus. On the
same annulus the disk retains its prescribed radial map and height. All normal
spaces are those of the actual disk derivative.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel

variable {N k : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector N} (D : DiskData b f)

theorem exists_normalFrame_collar (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)
    (a : Sphere 3 → Space N k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)
    (T : Vector 4 → Vector (k + 5) →L[ℝ] Vector (N + 6))
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (T x).range ≤ (fderiv ℝ D.toFun x).rangeᗮ)
    (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (a s).val) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ T' : Vector 4 → Vector (k + 5) →L[ℝ] Vector (N + 6),
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T' x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T' x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1,
          (T' x).range ≤ (fderiv ℝ D.toFun x).rangeᗮ) ∧
        (∀ s : Sphere 3, T' s.val = boundaryFrameOperator (a s).val) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
          D.toFun x = collar b f x ∧
          T' x = boundaryFrameOperator (a (SphereRadialRetraction.retract b x)).val := by
  let F := boundaryFrameExtension b a has
  have hFT (s : Sphere 3) : F s.val = T s.val :=
    (boundaryFrameExtension_coe b a has s).trans (hTb s).symm
  obtain ⟨V, hV, hSV, hDV⟩ := D.collar_eq
  let U := V ∩ {x : Vector 4 | (1 / 2 : ℝ) < ‖x‖}
  have hU : IsOpen U := hV.inter (isOpen_lt continuous_const continuous_norm)
  have hSU : sphere (0 : Vector 4) 1 ⊆ U := by
    intro x hx
    refine ⟨hSV hx, ?_⟩
    have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    change (1 / 2 : ℝ) < ‖x‖
    rw [hn]
    norm_num
  have hFn (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ U)
      (w : Vector (k + 5)) : ‖F x w‖ = ‖w‖ :=
    norm_boundaryFrameExtension b a has hx.2.2 w
  have hFr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ U) :
      (F x).range ≤ (fderiv ℝ D.toFun x).rangeᗮ :=
    boundaryFrameExtension_normal_disk b a has f hf ha hV hDV hx.2.1 hx.2.2
  obtain ⟨r, hr, hr1, hrU, T', hT's, hT'n, hT'r, hT'F⟩ :=
    exists_smoothDiskNormalFrame_collar D.toFun (fun _ _ ↦ D.smooth.contDiffAt)
      D.immersive T hTs hTn hTr F (contDiff_boundaryFrameExtension b a has)
      hFT hU hSU hFn hFr
  refine ⟨r, hr, hr1, T', hT's, hT'n, hT'r, ?_, ?_⟩
  · intro s
    have hrs : r ≤ ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hr1.le
    exact (hT'F s.val (sphere_subset_closedBall s.property) hrs).trans
      (boundaryFrameExtension_coe b a has s)
  · intro x hx hxr
    have hxU := hrU ⟨hx, hxr⟩
    exact ⟨hDV hxU.1, (hT'F x hx hxr).trans
      (boundaryFrameExtension_eq_radial b a has hxU.2)⟩

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
