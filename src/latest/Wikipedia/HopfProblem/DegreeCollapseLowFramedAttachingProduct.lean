import Wikipedia.HopfProblem.DegreeCollapseLowCompatibleCollarFrame

/-!

# Fully framed low-dimensional attaching products in the original native atlas

The actual embedded product map and its full normal frame both match the
original seven-manifold on a whole attaching collar. The native tube,
interior avoidance, disk core, and all collar data are constructed from the
original embedded low-dimensional sphere. Compactness removes the separate
tubular-retraction input. An attached trace or filling is not inferred.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

structure FramedAttachingProduct (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : NoExoticSixSphere.Sphere d → M) where
  disk : CollaredFramedDisk (spherePole d) (e.toFun ∘ f) (fun s => a.orthonormal (f s))
  map : Vector (d + 1) × Vector (7 - d) → Vector (e.ambientDimension + (1 + (1 + (d + 1))))
  map_core : ∀ x : Vector (d + 1), map (x, 0) = disk.map x
  innerRadius : ℝ
  innerRadius_pos : 0 < innerRadius
  innerRadius_lt_one : innerRadius < 1
  radius : ℝ
  radius_pos : 0 < radius
  embedded : IsClosedEmbedding
    (fun p : closedBall (0 : Vector (d + 1)) 1 × closedBall (0 : Vector (7 - d)) radius ↦
      map (p.1.val, p.2.val))
  smooth : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ v ∈ closedBall (0 : Vector (7 - d)) radius,
    ContDiffAt ℝ ∞ map (x, v)
  immersive : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ v ∈ closedBall (0 : Vector (7 - d)) radius,
    Injective (fderiv ℝ map (x, v))
  tube : NoExoticSixSphere.Sphere d × Vector (7 - d) → M
  tube_core : ∀ s : NoExoticSixSphere.Sphere d, tube (s, 0) = f s
  tube_embedded : IsClosedEmbedding
    (fun p : NoExoticSixSphere.Sphere d × closedBall (0 : Vector (7 - d)) radius ↦
      tube (p.1, p.2.val))
  tube_localDiffeomorph : ∀ s : NoExoticSixSphere.Sphere d,
    ∀ v ∈ closedBall (0 : Vector (7 - d)) radius,
    IsLocalDiffeomorphAt ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) ∞ tube (s, v)
  collar_map : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, innerRadius ≤ ‖x‖ →
    ∀ v ∈ closedBall (0 : Vector (7 - d)) radius,
      map (x, v) = coordinates e.ambientDimension (d + 1)
        ((e.toFun (tube (SphereRadialRetraction.retract (spherePole d) x, v)),
          definingFunction x), 0)
  interior_avoids : ∀ x ∈ ball (0 : Vector (d + 1)) 1, ∀ v ∈ closedBall (0 : Vector (7 - d)) radius,
    map (x, v) ∉ range (appendZeroMap e.ambientDimension (1 + (1 + (d + 1))))
  normalFrame : Vector (d + 1) × Vector (7 - d) →
    Vector ((e.ambientDimension - 7) + (1 + (d + 1))) →L[ℝ]
    Vector (e.ambientDimension + (1 + (1 + (d + 1))))
  normalFrame_smooth : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
    ∀ v ∈ closedBall (0 : Vector (7 - d)) radius, ContDiffAt ℝ ∞ normalFrame (x, v)
  normalFrame_norm : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
    ∀ v ∈ closedBall (0 : Vector (7 - d)) radius, ∀ w, ‖normalFrame (x, v) w‖ = ‖w‖
  normalFrame_range : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
    ∀ v ∈ closedBall (0 : Vector (7 - d)) radius,
      (normalFrame (x, v)).range = (fderiv ℝ map (x, v)).rangeᗮ
  collar_frame : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, innerRadius ≤ ‖x‖ →
    ∀ v ∈ closedBall (0 : Vector (7 - d)) radius,
      normalFrame (x, v) = boundaryFrameOperator d
        (a.orthonormal (tube (SphereRadialRetraction.retract (spherePole d) x, v))).val

namespace FramedAttachingProduct

variable {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

theorem map_boundary (s : NoExoticSixSphere.Sphere d) (v : Vector (7 - d))
    (hv : v ∈ closedBall 0 A.radius) :
    A.map (s.val, v) = appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
      (e.toFun (A.tube (s, v))) := by
  have hs : A.innerRadius ≤ ‖s.val‖ := by
    rw [ClosedHemisphere.unit_norm]
    exact A.innerRadius_lt_one.le
  rw [A.collar_map s.val (sphere_subset_closedBall s.property) hs v hv,
    SphereRadialRetraction.retract_coe,
    (definingFunction_eq_zero_iff s.val).mpr s.property, coordinates_old]

theorem normalFrame_boundary (s : NoExoticSixSphere.Sphere d) (v : Vector (7 - d))
    (hv : v ∈ closedBall 0 A.radius) : A.normalFrame (s.val, v) =
      boundaryFrameOperator d (a.orthonormal (A.tube (s, v))).val := by
  have hs : A.innerRadius ≤ ‖s.val‖ := by
    rw [ClosedHemisphere.unit_norm]
    exact A.innerRadius_lt_one.le
  rw [A.collar_frame s.val (sphere_subset_closedBall s.property) hs v hv,
    SphereRadialRetraction.retract_coe]

end FramedAttachingProduct

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

theorem nonempty_framedAttachingProduct (hdim : 0 < d) (hsmall : d ≤ 3)
    (R : EuclideanEmbedding.TubularRetraction e) (f : NoExoticSixSphere.Sphere d → M)
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s)) :
    Nonempty (FramedAttachingProduct e a f) := by
  obtain ⟨D, r, hr, hr1, A, χ, hχin, hχout, B, hc, hemb, hlocal, _, hmapc, havoid⟩ :=
    exists_curvedAttachingProduct e a hdim hsmall R f hf hi hd
  have hχ : (1 / 2 : ℝ) < χ.rOut := by rw [hχout]; linarith
  have hχ1 : χ.rOut < 1 := by rw [hχout]; linarith
  have hrχ : r ≤ χ.rOut := by rw [← hχin]; exact χ.rIn_lt_rOut.le
  have hc' (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1)
      (hxr : χ.rOut ≤ ‖x‖) := hc x hx (hrχ.trans hxr)
  obtain ⟨q, hqχ, hq1, ε, hε, hεB, G, hG, hGc⟩ :=
    exists_compatible_curvedCollarFrame e a f hf hd D.toFramedDisk A R χ B hχ hχ1 hc'
      (fun s v hv ↦ (hlocal s v hv).1)
  refine ⟨{
    disk := D
    map := curvedDiskProduct e f D.toFramedDisk A R χ
    map_core := curvedDiskProduct_core e f D.toFramedDisk A R χ
    innerRadius := q
    innerRadius_pos := by linarith
    innerRadius_lt_one := hq1
    radius := ε
    radius_pos := hε
    embedded := LowDiskThickening.restrict_closedProduct_embedding
      (fun p : closedBall (0 : Vector (d + 1)) 1 × Vector (7 - d) ↦
        curvedDiskProduct e f D.toFramedDisk A R χ (p.1.val, p.2)) hεB B.embedded
    smooth := fun x hx v hv ↦ B.smooth x hx v ((closedBall_subset_closedBall hεB) hv)
    immersive := fun x hx v hv ↦ B.immersive x hx v ((closedBall_subset_closedBall hεB) hv)
    tube := internalSphereTube e f A.boundaryTransverse R
    tube_core := internalSphereTube_core e f A.boundaryTransverse R
    tube_embedded := LowDiskThickening.restrict_closedProduct_embedding
      (internalSphereTube e f A.boundaryTransverse R) hεB hemb
    tube_localDiffeomorph := fun s v hv ↦ (hlocal s v ((closedBall_subset_closedBall hεB) hv)).2
    collar_map := ?_
    interior_avoids := fun x hx v hv ↦ havoid x hx v ((closedBall_subset_closedBall hεB) hv)
    normalFrame := G
    normalFrame_smooth := fun x hx v hv ↦ (hG x hx v hv).1
    normalFrame_norm := fun x hx v hv ↦ (hG x hx v hv).2.1
    normalFrame_range := fun x hx v hv ↦ (hG x hx v hv).2.2
    collar_frame := ?_ }⟩
  · intro x hx hxq v _hv
    exact hmapc x hx (hqχ.le.trans hxq) v
  · intro x hx hxq v hv
    exact hGc x hx hxq v hv

theorem nonempty_framedAttachingProduct_of_compact [CompactSpace M]
    (hdim : 0 < d) (hsmall : d ≤ 3) (f : NoExoticSixSphere.Sphere d → M)
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s)) :
    Nonempty (FramedAttachingProduct e a f) := by
  let : Nonempty M := ⟨f (spherePole d)⟩
  obtain ⟨R⟩ := e.nonempty_tubularRetraction a
  exact nonempty_framedAttachingProduct e a hdim hsmall R f hf hi hd

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
