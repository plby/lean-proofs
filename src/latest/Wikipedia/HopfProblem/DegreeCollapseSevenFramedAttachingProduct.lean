import Wikipedia.HopfProblem.DegreeCollapseSevenCompatibleCollarFrame

/-!
# SevenFramedAttachingProduct

The actual map and its full normal frame match the original seven-manifold on a whole attaching collar. The embedded product, native tube, interior avoidance, and exact collar values are constructed from an embedded S3, its induced frame, and an explicitly supplied retraction. No filling or attached trace is inferred.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

structure FramedAttachingProduct (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel) (f : Sphere 3 → M) where
  disk : DiskData (pole 3) (e.toFun ∘ f)
  map : Vector 4 × Vector 4 → Vector (e.ambientDimension + 6)
  map_core : ∀ x : Vector 4, map (x, 0) = disk.toFun x
  innerRadius : ℝ
  innerRadius_pos : 0 < innerRadius
  innerRadius_lt_one : innerRadius < 1
  radius : ℝ
  radius_pos : 0 < radius
  embedded : IsClosedEmbedding
    (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector 4) radius ↦
      map (p.1.val, p.2.val))
  smooth : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) radius,
    ContDiffAt ℝ ∞ map (x, v)
  immersive : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) radius,
    Injective (fderiv ℝ map (x, v))
  tube : Sphere 3 × Vector 4 → M
  tube_core : ∀ s : Sphere 3, tube (s, 0) = f s
  tube_embedded : IsClosedEmbedding
    (fun p : Sphere 3 × closedBall (0 : Vector 4) radius ↦ tube (p.1, p.2.val))
  tube_localDiffeomorph : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) radius,
    IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞ tube (s, v)
  collar_map : ∀ x ∈ closedBall (0 : Vector 4) 1, innerRadius ≤ ‖x‖ →
    ∀ v ∈ closedBall (0 : Vector 4) radius,
      map (x, v) = coordinates e.ambientDimension 4
        ((e.toFun (tube (SphereRadialRetraction.retract (pole 3) x, v)), definingFunction x), 0)
  interior_avoids : ∀ x ∈ ball (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) radius,
    map (x, v) ∉ range (appendZeroMap e.ambientDimension 6)
  normalFrame : Vector 4 × Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)
  normalFrame_smooth : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector 4) radius, ContDiffAt ℝ ∞ normalFrame (x, v)
  normalFrame_norm : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector 4) radius, ∀ w, ‖normalFrame (x, v) w‖ = ‖w‖
  normalFrame_range : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector 4) radius,
      (normalFrame (x, v)).range = (fderiv ℝ map (x, v)).rangeᗮ
  collar_frame : ∀ x ∈ closedBall (0 : Vector 4) 1, innerRadius ≤ ‖x‖ →
    ∀ v ∈ closedBall (0 : Vector 4) radius,
      normalFrame (x, v) = boundaryFrameOperator
        (a.orthonormal (tube (SphereRadialRetraction.retract (pole 3) x, v))).val

namespace FramedAttachingProduct

variable {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem map_boundary (s : Sphere 3) (v : Vector 4) (hv : v ∈ closedBall 0 A.radius) :
    A.map (s.val, v) = appendZeroMap e.ambientDimension 6 (e.toFun (A.tube (s, v))) := by
  have hs : A.innerRadius ≤ ‖s.val‖ := by
    rw [ClosedHemisphere.unit_norm]
    exact A.innerRadius_lt_one.le
  rw [A.collar_map s.val (sphere_subset_closedBall s.property) hs v hv,
    SphereRadialRetraction.retract_coe,
    (definingFunction_eq_zero_iff s.val).mpr s.property, coordinates_old]

theorem normalFrame_boundary (s : Sphere 3) (v : Vector 4)
    (hv : v ∈ closedBall 0 A.radius) : A.normalFrame (s.val, v) =
      boundaryFrameOperator (a.orthonormal (A.tube (s, v))).val := by
  have hs : A.innerRadius ≤ ‖s.val‖ := by
    rw [ClosedHemisphere.unit_norm]
    exact A.innerRadius_lt_one.le
  rw [A.collar_frame s.val (sphere_subset_closedBall s.property) hs v hv,
    SphereRadialRetraction.retract_coe]

end FramedAttachingProduct

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

theorem nonempty_framedAttachingProduct (R : EuclideanEmbedding.TubularRetraction e) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    Nonempty (FramedAttachingProduct e a f) := by
  obtain ⟨D, r, hr, hr1, T, A, χ, hχin, hχout, B, hTb, hc, hemb, hlocal, _, havoid⟩ :=
    SevenSurgery.exists_curvedAttachingProduct e a R f hf hi hd
  have hχ : (1 / 2 : ℝ) < χ.rOut := by rw [hχout]; linarith
  have hχ1 : χ.rOut < 1 := by rw [hχout]; linarith
  have hrχ : r ≤ χ.rOut := by rw [← hχin]; exact χ.rIn_lt_rOut.le
  have hc' (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut ≤ ‖x‖) :
      D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
      T x = boundaryFrameOperator
        (SevenSurgery.normalFrameOnSphere e a f (SphereRadialRetraction.retract (pole 3) x)).val ∧
      A.transverse x = A.transverse (SphereRadialRetraction.retract (pole 3) x).val :=
    hc x hx (hrχ.trans hxr)
  obtain ⟨q, hqχ, hq1, ε, hε, hεB, G, hG, hGc⟩ :=
    SevenSurgery.exists_compatible_curvedCollarFrame e a f hf hd D A R χ B hTb hχ hχ1 hc'
      (fun s v hv ↦ (hlocal s v hv).1)
  refine ⟨{
    disk := D
    map := SevenSurgery.curvedDiskProduct e f D A R χ
    map_core := SevenSurgery.curvedDiskProduct_core e f D A R χ
    innerRadius := q
    innerRadius_pos := by linarith
    innerRadius_lt_one := hq1
    radius := ε
    radius_pos := hε
    embedded := GeneralDiskThickening.restrict_closedProduct_embedding
      (fun p : closedBall (0 : Vector 4) 1 × Vector 4 ↦
        SevenSurgery.curvedDiskProduct e f D A R χ (p.1.val, p.2)) hεB B.embedded
    smooth := fun x hx v hv ↦ B.smooth x hx v ((closedBall_subset_closedBall hεB) hv)
    immersive := fun x hx v hv ↦ B.immersive x hx v ((closedBall_subset_closedBall hεB) hv)
    tube := SevenSurgery.internalSphereTube e f A.boundaryTransverse R
    tube_core := SevenSurgery.internalSphereTube_core e f A.boundaryTransverse R
    tube_embedded := GeneralDiskThickening.restrict_closedProduct_embedding
      (SevenSurgery.internalSphereTube e f A.boundaryTransverse R) hεB hemb
    tube_localDiffeomorph := fun s v hv ↦ (hlocal s v ((closedBall_subset_closedBall hεB) hv)).2
    collar_map := ?_
    interior_avoids := fun x hx v hv ↦ havoid x hx v ((closedBall_subset_closedBall hεB) hv)
    normalFrame := G
    normalFrame_smooth := fun x hx v hv ↦ (hG x hx v hv).1
    normalFrame_norm := fun x hx v hv ↦ (hG x hx v hv).2.1
    normalFrame_range := fun x hx v hv ↦ (hG x hx v hv).2.2
    collar_frame := ?_ }⟩
  · intro x hx hxq v _hv
    have hxr : χ.rOut ≤ ‖x‖ := hqχ.le.trans hxq
    exact SevenSurgery.curvedDiskProduct_collar e a f hf hd D A R χ hTb (hχ.trans_le hxr) hxr
      (hc' x hx hxr).1 (hc' x hx hxr).2.2 v
  · intro x hx hxq v hv
    exact hGc x hx hxq v hv

theorem nonempty_framedAttachingProduct_of_compact [CompactSpace M] (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    Nonempty (FramedAttachingProduct e a f) := by
  letI : Nonempty M := ⟨f (pole 3)⟩
  obtain ⟨R⟩ := e.nonempty_tubularRetraction a
  exact nonempty_framedAttachingProduct e a R f hf hi hd

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
