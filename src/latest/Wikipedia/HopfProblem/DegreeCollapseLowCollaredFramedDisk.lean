import Wikipedia.HopfProblem.DegreeCollapseLowFramedSpanningDisk
import Wikipedia.HopfProblem.DegreeCollapseLowRadialNormalFrame
import Wikipedia.HopfProblem.DegreeCollapseLowDiskNormalCollar

/-!

# Constructed low-surgery disks retain the original whole radial frame collar

Upgrade the actual embedded spanning disk without changing its map. Its
normal frame now agrees with the prescribed original normal columns and
graph axes on a whole inner annulus, not only on the boundary sphere.
The disk, exact native boundary map, interior avoidance, and full radial
map collar are retained. This constructs the core framing data needed
before thickening and attaching the low-connectivity surgery trace.
-/

noncomputable section

open Set Metric Function Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

structure CollaredFramedDisk {d N k : ℕ} (b : NoExoticSixSphere.Sphere d)
    (f : NoExoticSixSphere.Sphere d → Vector N)
    (a : NoExoticSixSphere.Sphere d → Space N k) extends FramedDisk b f a where
  collarRadius : ℝ
  collarRadius_pos : 0 < collarRadius
  collarRadius_lt_one : collarRadius < 1
  map_radial : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, collarRadius ≤ ‖x‖ →
    map x = collar b f x
  frame_radial : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, collarRadius ≤ ‖x‖ →
    frame x = boundaryFrameOperator d (a (SphereRadialRetraction.retract b x)).val

namespace FramedDisk

variable {d N k : ℕ} {b : NoExoticSixSphere.Sphere d}
  {f : NoExoticSixSphere.Sphere d → Vector N}
  {a : NoExoticSixSphere.Sphere d → Space N k} (D : FramedDisk b f a)

theorem exists_collared_upgrade (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f)
    (has : ContMDiff (𝓡 d) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s => (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 d) (𝓡 N) f s).rangeᗮ) :
    ∃ C : CollaredFramedDisk b f a, C.map = D.map := by
  let F := boundaryFrameExtension b a has
  have hFT (s : NoExoticSixSphere.Sphere d) : F s.val = D.frame s.val :=
    (boundaryFrameExtension_coe b a has s).trans (D.frame_boundary s).symm
  let U := D.collarSet ∩ {x : Vector (d + 1) | (1 / 2 : ℝ) < ‖x‖}
  have hU : IsOpen U := D.collar_open.inter (isOpen_lt continuous_const continuous_norm)
  have hSU : sphere (0 : Vector (d + 1)) 1 ⊆ U := by
    intro x hx
    refine ⟨D.boundary_in_collar hx, ?_⟩
    have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    change (1 / 2 : ℝ) < ‖x‖
    rw [hn]
    norm_num
  have hFn (x : Vector (d + 1))
      (hx : x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ U)
      (w : Vector (k + (1 + (d + 1)))) : ‖F x w‖ = ‖w‖ :=
    norm_boundaryFrameExtension b a has hx.2.2 w
  have hFr (x : Vector (d + 1))
      (hx : x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ U) :
      (F x).range ≤ (fderiv ℝ D.map x).rangeᗮ :=
    boundaryFrameExtension_normal_disk b a has f hf ha
      D.collar_open D.collar_eq hx.2.1 hx.2.2
  obtain ⟨r, hr, hr1, hrU, T, hTs, hTn, hTr, hTF⟩ :=
    LowDiskNormal.exists_smooth_frame_collar D.map (fun _ _ => D.smooth.contDiffAt)
      D.immersive D.frame D.frame_smooth D.frame_norm D.frame_normal F
      (contDiff_boundaryFrameExtension b a has) hFT hU hSU hFn hFr
  have hTb (s : NoExoticSixSphere.Sphere d) : T s.val = boundaryFrameOperator d (a s).val := by
    have hrs : r ≤ ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hr1.le
    exact (hTF s.val (sphere_subset_closedBall s.property) hrs).trans
      (boundaryFrameExtension_coe b a has s)
  refine ⟨{
    toFramedDisk := { D with
      frame := T
      frame_smooth := hTs
      frame_norm := hTn
      frame_normal := hTr
      frame_boundary := hTb }
    collarRadius := r
    collarRadius_pos := hr
    collarRadius_lt_one := hr1
    map_radial := ?_
    frame_radial := ?_ }, rfl⟩
  · intro x hx hxr
    exact D.collar_eq (hrU ⟨hx, hxr⟩).1
  · intro x hx hxr
    exact (hTF x hx hxr).trans (boundaryFrameExtension_eq_radial b a has (hrU ⟨hx, hxr⟩).2)

end FramedDisk

theorem nonempty_collaredFramedDisk {d N k : ℕ} (hd : 0 < d) (hN : k + 2 * d + 1 ≤ N)
    (b : NoExoticSixSphere.Sphere d) (f : NoExoticSixSphere.Sphere d → Vector N)
    (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f) (hi : Injective f)
    (hdf : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 N) f s))
    (a : NoExoticSixSphere.Sphere d → Space N k)
    (has : ContMDiff (𝓡 d) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s => (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 d) (𝓡 N) f s).rangeᗮ) :
    Nonempty (CollaredFramedDisk b f a) := by
  obtain ⟨D⟩ := nonempty_framedDisk hd hN b f hf hi hdf a has ha
  obtain ⟨C, _⟩ := D.exists_collared_upgrade hf has ha
  exact ⟨C⟩

theorem nonempty_native_collaredFramedDisk {d : ℕ} (hd : 0 < d) (hsmall : d ≤ 3)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
    (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : NoExoticSixSphere.Sphere d → M)
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
    (hdf : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s)) :
    Nonempty (CollaredFramedDisk (spherePole d)
      (e.toFun ∘ f) (fun s => a.orthonormal (f s))) := by
  obtain ⟨D⟩ := nonempty_native_framedDisk hd hsmall e a f hf hi hdf
  obtain ⟨C, _⟩ := D.exists_collared_upgrade (e.smooth.comp hf)
    (a.contMDiff_orthonormal.comp hf) (by
      intro s
      rw [a.orthonormal_range, e.range_normalProjection]
      apply Submodule.orthogonal_le
      rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
        (hf.mdifferentiableAt (by simp))]
      rintro _ ⟨v, rfl⟩
      exact ⟨_, rfl⟩)
  exact ⟨C⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
