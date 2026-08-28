import Wikipedia.HopfProblem.DegreeCollapseLowDiskNormalExtension
import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryBoundaryFrame
import Wikipedia.NoExoticSixSphere.SmoothRangeOrthonormalization
import Wikipedia.NoExoticSixSphere.NormalBundle

/-!

# Constructed spanning disks with the original low-surgery normal columns

For an actual embedded immersive sphere, construct its stabilized smooth
embedded spanning disk with interior disjoint from the entire original
ambient space. The prescribed old normal columns and graph axes extend
smoothly in the actual disk normal spaces and retain exact boundary values.
The disk keeps its full original radial collar as a map.

In a normally framed seven-manifold this construction applies to spheres
of dimensions one, two and three without a supplied framing obstruction
or disk. Thickening and attaching the low-dimensional surgery trace still
remain necessary; this disk alone does not establish low connectivity.
-/

noncomputable section

open Set Metric Function Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

structure FramedDisk {d N k : ℕ} (b : NoExoticSixSphere.Sphere d)
    (f : NoExoticSixSphere.Sphere d → Vector N)
    (a : NoExoticSixSphere.Sphere d → Space N k) where
  map : Vector (d + 1) → Vector (N + (1 + (1 + (d + 1))))
  smooth : ContDiff ℝ ∞ map
  embedded : IsClosedEmbedding
    (fun x : closedBall (0 : Vector (d + 1)) 1 => map x.val)
  immersive : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, Injective (fderiv ℝ map x)
  boundary : ∀ s, map s.val = appendZeroMap N (1 + (1 + (d + 1))) (f s)
  interior_avoids : ∀ x ∈ ball (0 : Vector (d + 1)) 1,
    map x ∉ range (appendZeroMap N (1 + (1 + (d + 1))))
  collarSet : Set (Vector (d + 1))
  collar_open : IsOpen collarSet
  boundary_in_collar : sphere 0 1 ⊆ collarSet
  collar_eq : EqOn map (collar b f) collarSet
  frame : Vector (d + 1) → Vector (k + (1 + (d + 1))) →L[ℝ]
    Vector (N + (1 + (1 + (d + 1))))
  frame_smooth : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ frame x
  frame_norm : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖frame x w‖ = ‖w‖
  frame_normal : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
    (frame x).range ≤ (fderiv ℝ map x).rangeᗮ
  frame_boundary : ∀ s, frame s.val = boundaryFrameOperator d (a s).val

theorem nonempty_framedDisk {d N k : ℕ} (hd : 0 < d) (hN : k + 2 * d + 1 ≤ N)
    (b : NoExoticSixSphere.Sphere d) (f : NoExoticSixSphere.Sphere d → Vector N)
    (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f) (hi : Injective f)
    (hdf : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 N) f s))
    (a : NoExoticSixSphere.Sphere d → Space N k)
    (has : ContMDiff (𝓡 d) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s => (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 d) (𝓡 N) f s).rangeᗮ) :
    Nonempty (FramedDisk b f a) := by
  obtain ⟨G, hG, hGe, hGi, hGb, hGa, V, hV, hSV, hGv⟩ :=
    exists_spanningDisk b f hf hi hdf
  let A : C(NoExoticSixSphere.Sphere d,
      Space (N + (1 + (1 + (d + 1)))) (k + (1 + (d + 1)))) :=
    ⟨fun s => boundaryFrame d (a s),
      (contMDiff_boundaryFrameOperator d has).continuous.subtype_mk _⟩
  have hAr (s : NoExoticSixSphere.Sphere d) :
      (A s).val.range ≤ (fderiv ℝ G s.val).rangeᗮ :=
    boundaryFrame_normal_disk b f hf a ha hV hSV hGv s
  obtain ⟨T, hTs, hTn, hTr, hTb⟩ := LowDiskNormal.exists_smooth_extension hd
    (by omega : (k + (1 + (d + 1))) + 2 * (d + 1) ≤ N + (1 + (1 + (d + 1))))
    G (fun _ _ => hG.contDiffAt) hGi A (contMDiff_boundaryFrameOperator d has) hAr
  exact ⟨{
    map := G
    smooth := hG
    embedded := hGe
    immersive := hGi
    boundary := hGb
    interior_avoids := hGa
    collarSet := V
    collar_open := hV
    boundary_in_collar := hSV
    collar_eq := hGv
    frame := T
    frame_smooth := hTs
    frame_norm := hTn
    frame_normal := hTr
    frame_boundary := hTb }⟩

theorem nonempty_native_framedDisk {d : ℕ} (hd : 0 < d) (hsmall : d ≤ 3)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
    (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : NoExoticSixSphere.Sphere d → M)
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
    (hdf : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s)) :
    Nonempty (FramedDisk (spherePole d) (e.toFun ∘ f) (fun s => a.orthonormal (f s))) := by
  have hdim := e.dimension_le_ambient (f (spherePole d))
  apply nonempty_framedDisk hd
    (by omega : (e.ambientDimension - 7) + 2 * d + 1 ≤ e.ambientDimension)
    (spherePole d) (e.toFun ∘ f) (e.smooth.comp hf) (e.closedEmbedding.injective.comp hi)
    ?_ (fun s => a.orthonormal (f s)) (a.contMDiff_orthonormal.comp hf) ?_
  · intro s
    rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
    exact (e.injective_mfderiv (f s)).comp (hdf s)
  · intro s
    rw [a.orthonormal_range, e.range_normalProjection]
    apply Submodule.orthogonal_le
    rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
    rintro _ ⟨v, rfl⟩
    exact ⟨_, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
