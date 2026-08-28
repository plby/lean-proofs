import Wikipedia.HopfProblem.DegreeCollapseSmoothEvenFrameTwist
import Wikipedia.NoExoticSixSphere.PartialFrameBlockIteration
import Wikipedia.NoExoticSixSphere.SphereDiskExtension
import Wikipedia.NoExoticSixSphere.SmoothDiskFrameExtension
import Wikipedia.NoExoticSixSphere.SmoothDiskCollarFrame
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialCollar

/-!
# Disk extensions of the actual coordinate-block frame twists

The stable contraction uses a chosen orthogonal splitting. The attaching
geometry instead uses literal Euclidean coordinate blocks. A fixed isometric
change of coordinates identifies the two constructions, without identifying
independently chosen complement bases. Any positive identity block therefore
gives a continuous disk extension. Relative frame smoothing retains the exact
original boundary operators.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.StableTwistDiskExtension

open NoExoticSixSphere GLOrthonormalization OrthogonalPaths OrthogonalStabilization
open Stiefel DiskBoundary

variable {n : ℕ}

def forget (a : OrthogonalOperators n) : Stiefel.Space n n := ⟨a.1.1, a.2⟩

def forgetMap : C(OrthogonalOperators n, Stiefel.Space n n) :=
  ⟨forget, (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def blockFamily {X : Type*} [TopologicalSpace X] (k : ℕ)
    (a : C(X, OrthogonalOperators n)) : C(X, Stiefel.Space (n + k) (n + k)) :=
  (Stiefel.BlockSum.map k).comp (forgetMap.comp a)

theorem contMDiff_blockFamily {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] (k : ℕ)
    (a : C(M, OrthogonalOperators n))
    (ha : ContMDiff I 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞ (fun x ↦ (a x).1.1)) :
    ContMDiff I 𝓘(ℝ, Vector (n + k) →L[ℝ] Vector (n + k)) ∞
      (fun x ↦ (blockFamily k a x).val) :=
  contMDiff_const.clm_comp ((ha.clm_prodMap contMDiff_const).clm_comp contMDiff_const)

local instance (r : ℕ) : Fact (Module.finrank ℝ (Vector (r + 1)) = r + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def coordinateChange (z : UnitSphere (Vector (n + 1))) :
    C(OrthogonalOperators (n + 1), Stiefel.Space (n + 1) (n + 1)) :=
  (Stiefel.FrameCoordinates.homeomorph
    ((NoExoticSixSphere.ColumnCoordinates.split z).trans (EuclideanTailCoordinates.split n).symm)
    ((EuclideanTailCoordinates.split n).trans (NoExoticSixSphere.ColumnCoordinates.split z).symm) :
      C(Stiefel.Space (n + 1) (n + 1), Stiefel.Space (n + 1) (n + 1))).comp forgetMap

theorem coordinateChange_stabilize (z : UnitSphere (Vector (n + 1)))
    (a : OrthogonalOperators n) :
    coordinateChange z (stabilize z a) = Stiefel.BlockSum.frame 1 (forget a) := by
  rw [Stiefel.BlockSum.frame_one_eq_split,
    Stiefel.SplitReconstruction.reconstruct_eq_coordinates
      (EuclideanTailCoordinates.split n) (EuclideanTailCoordinates.split n) z z]
  congr 1

theorem coordinateChange_identity (z : UnitSphere (Vector (n + 1))) :
    coordinateChange z (identity (n + 1)) = forget (identity (n + 1)) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  change (EuclideanTailCoordinates.split n).symm
      ((NoExoticSixSphere.ColumnCoordinates.split z)
        ((NoExoticSixSphere.ColumnCoordinates.split z).symm
          (EuclideanTailCoordinates.split n w))) = w
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]

theorem one_block_nullhomotopic {X : Type*} [TopologicalSpace X]
    (z : UnitSphere (Vector (n + 1))) (a : C(X, OrthogonalOperators n))
    (h : (stabilizeMap z a).Homotopic (ContinuousMap.const X (identity (n + 1)))) :
    (blockFamily 1 a).Homotopic (ContinuousMap.const X (forget (identity (n + 1)))) := by
  have H := (ContinuousMap.Homotopic.refl (coordinateChange z)).comp h
  have hs : (coordinateChange z).comp (stabilizeMap z a) = blockFamily 1 a := by
    apply ContinuousMap.ext
    intro x
    exact coordinateChange_stabilize z (a x)
  have he : (coordinateChange z).comp (ContinuousMap.const X (identity (n + 1))) =
      ContinuousMap.const X (forget (identity (n + 1))) := by
    apply ContinuousMap.ext
    intro x
    exact coordinateChange_identity z
  rwa [hs, he] at H

/-- The actual coordinate block extends for every positive number of added columns. -/
theorem block_extends (z : UnitSphere (Vector (n + 1)))
    (a : C(Sphere 3, OrthogonalOperators n))
    (h : (stabilizeMap z a).Homotopic (ContinuousMap.const _ (identity (n + 1))))
    (k : ℕ) (hk : 0 < k) : Extends (blockFamily k a) := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero =>
          apply (extends_homotopic_iff (one_block_nullhomotopic z a h)).mpr
          exact ⟨ContinuousMap.const _ (forget (identity (n + 1))), fun _ ↦ rfl⟩
      | succ j =>
          obtain ⟨F, hF⟩ := ih (by omega)
          refine ⟨(Stiefel.BlockSum.map 1).comp F, ?_⟩
          intro s
          change Stiefel.BlockSum.frame 1 (F (DiskCylinder.boundaryToDisk s)) = _
          rw [hF]
          exact Stiefel.BlockSum.frame_succ (j + 1) (forget (a s))

/-- Smooth disk operators retain every prescribed boundary block exactly. -/
theorem exists_smooth_block_extension (z : UnitSphere (Vector (n + 1)))
    (a : C(Sphere 3, OrthogonalOperators n))
    (ha : ContMDiff (𝓡 3) 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞ (fun s ↦ (a s).1.1))
    (h : (stabilizeMap z a).Homotopic (ContinuousMap.const _ (identity (n + 1))))
    (k : ℕ) (hk : 0 < k) :
    ∃ Q : Vector 4 → Vector (n + k) →L[ℝ] Vector (n + k),
      (∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ Q x) ∧
      (∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ∀ w, ‖Q x w‖ = ‖w‖) ∧
      ∀ s : Sphere 3, Q s.val = Stiefel.BlockSum.operator k (a s).1.1 := by
  obtain ⟨F, hF⟩ := block_extends z a h k hk
  obtain ⟨Q, hQs, hQn, -, hQb⟩ := Stiefel.exists_smoothDiskFrame_extension
    (fun _ : Vector 4 ↦ ContinuousLinearMap.id ℝ (Vector (n + k)))
    (fun _ _ ↦ by
      change (1 : Vector (n + k) →L[ℝ] Vector (n + k)) * 1 = 1
      exact one_mul _) (fun _ _ ↦ contDiffAt_const)
    (blockFamily k a) (contMDiff_blockFamily k a ha) F
    (fun _ ↦ by simp) hF
  exact ⟨Q, hQs, hQn, hQb⟩

/-- The extension can retain the precise radial block on a whole inner collar. -/
theorem exists_smooth_block_collar_extension (b : Sphere 3)
    (z : UnitSphere (Vector (n + 1))) (a : C(Sphere 3, OrthogonalOperators n))
    (ha : ContMDiff (𝓡 3) 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞ (fun s ↦ (a s).1.1))
    (h : (stabilizeMap z a).Homotopic (ContinuousMap.const _ (identity (n + 1))))
    (k : ℕ) (hk : 0 < k) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ Q : Vector 4 → Vector (n + k) →L[ℝ] Vector (n + k),
        (∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ Q x) ∧
        (∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ∀ w, ‖Q x w‖ = ‖w‖) ∧
        ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
          Q x = Stiefel.BlockSum.operator k (a (SphereRadialRetraction.retract b x)).1.1 := by
  obtain ⟨A, hA⟩ := block_extends z a h k hk
  let F : C(Vector 4, Vector (n + k) →L[ℝ] Vector (n + k)) :=
    ⟨SmoothSphereAmbient.extension b (fun s ↦ (blockFamily k a s).val),
      (SmoothSphereAmbient.contDiff_extension b (fun s ↦ (blockFamily k a s).val)
        (contMDiff_blockFamily k a ha)).continuous⟩
  have hFs : ContDiff ℝ ∞ F :=
    SmoothSphereAmbient.contDiff_extension b (fun s ↦ (blockFamily k a s).val)
      (contMDiff_blockFamily k a ha)
  have hFA (s : Sphere 3) : F s.val = (A (DiskCylinder.boundaryToDisk s)).val := by
    rw [hA]
    exact SmoothSphereAmbient.extension_coe b (fun t ↦ (blockFamily k a t).val) s
  let V : Set (Vector 4) := {x | (1 / 2 : ℝ) < ‖x‖}
  have hV : IsOpen V := isOpen_lt continuous_const continuous_norm
  have hSV : Metric.sphere (0 : Vector 4) 1 ⊆ V := by
    intro x hx
    change (1 / 2 : ℝ) < ‖x‖
    rw [show ‖x‖ = 1 by simpa only [Metric.mem_sphere, dist_zero_right] using hx]
    norm_num
  have hrad (x : Vector 4) (hx : x ∈ V) :
      F x = (blockFamily k a (SphereRadialRetraction.retract b x)).val :=
    SmoothSphereAmbient.extension_eq_radial_of_half_le b
      (fun s ↦ (blockFamily k a s).val) hx.le
  have hFn (x : Vector 4) (hx : x ∈ Metric.closedBall (0 : Vector 4) 1 ∩ V)
      (w : Vector (n + k)) : ‖F x w‖ = ‖w‖ := by
    rw [hrad x hx.2]
    exact (blockFamily k a (SphereRadialRetraction.retract b x)).property w
  obtain ⟨r, hr, hr1, hrV, Q, hQs, hQn, -, hQF⟩ := Stiefel.exists_smoothDiskFrame_collar
    (fun _ : Vector 4 ↦ ContinuousLinearMap.id ℝ (Vector (n + k)))
    (fun _ _ ↦ by
      change (1 : Vector (n + k) →L[ℝ] Vector (n + k)) * 1 = 1
      exact one_mul _) (fun _ _ ↦ contDiffAt_const) A (fun _ ↦ by simp)
    F hFs hFA hV hSV hFn (fun _ _ ↦ by simp)
  refine ⟨r, hr, hr1, Q, hQs, hQn, ?_⟩
  intro x hx hxr
  exact (hQF x hx hxr).trans (hrad x (hrV ⟨hx, hxr⟩))

end Wikipedia.HopfProblem.DegreeCollapse.StableTwistDiskExtension
