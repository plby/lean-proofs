import Wikipedia.HopfProblem.DegreeCollapseSmoothDiskPartialFrame
import Wikipedia.NoExoticSixSphere.SphereNeighborhoodAnnulus

/-!

# Prescribed whole-collar smoothing on disks of every dimension

Install the supplied smooth frame on an actual closed inner annulus.
Interpolation and relative smoothing preserve the original projection
ranges, exact collar columns and orthonormality. The disk dimension is
explicit, so this applies to the disks needed for low-connectivity surgery.
-/

noncomputable section

open Set Metric
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskPartialFrame

open NoExoticSixSphere GLOrthonormalization Stiefel
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {d N n : ℕ}

theorem exists_smooth_frame_collar
    (P : Vector (d + 1) → Vector N →L[ℝ] Vector N)
    (hP : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, IsIdempotentElem (P x))
    (hPs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ P x)
    (A : C(Disk (E := Vector (d + 1)), Space N n))
    (hAr : ∀ x, (A x).val.range ≤ (P x.val).range)
    (F : C(Vector (d + 1), Vector n →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
    (hFA : ∀ s : NoExoticSixSphere.Sphere d, F s.val = (A (boundaryToDisk s)).val)
    {V : Set (Vector (d + 1))} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
    (hFn : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ V, ∀ w, ‖F x w‖ = ‖w‖)
    (hFr : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ V, (F x).range ≤ (P x).range) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector (d + 1)) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ T : Vector (d + 1) → Vector n →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, (T x).range ≤ (P x).range) ∧
      ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖x‖ → T x = F x := by
  let Ac : C(Disk (E := Vector (d + 1)), Vector n →L[ℝ] Vector N) :=
    ⟨fun x ↦ (A x).val, continuous_subtype_val.comp A.continuous⟩
  obtain ⟨A₀, hA₀⟩ := Ac.exists_restrict_eq isClosed_closedBall
  have heA (x : Disk (E := Vector (d + 1))) : A₀ x.val = (A x).val :=
    ContinuousMap.congr_fun hA₀ x
  have heF : EqOn F A₀ (sphere (0 : Vector (d + 1)) 1) := by
    intro x hx
    exact (hFA ⟨x, hx⟩).trans (heA (boundaryToDisk ⟨x, hx⟩)).symm
  have hPA (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      (P x).comp (A₀ x) = A₀ x := by
    rw [heA ⟨x, hx⟩]
    apply ContinuousLinearMap.ext
    intro w
    exact projection_apply_range (P x) (hP x hx)
      ⟨(A ⟨x, hx⟩).val w, hAr ⟨x, hx⟩ ⟨w, rfl⟩⟩
  have hAi (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      Function.Injective ((P x).comp (A₀ x)) := by
    rw [hPA x hx, heA ⟨x, hx⟩]
    exact Stiefel.injective (A ⟨x, hx⟩)
  have hPc : ContinuousOn P (closedBall (0 : Vector (d + 1)) 1) :=
    fun x hx ↦ (hPs x hx).continuousAt.continuousWithinAt
  obtain ⟨B, hBi, U, hU, hSU, hBF⟩ := exists_boundaryInterpolation
    (isCompact_closedBall (0 : Vector (d + 1)) 1) (isCompact_sphere (0 : Vector (d + 1)) 1)
    A₀ F P hPc hAi heF
  obtain ⟨r, hr, hr1, hS⟩ := exists_annulus_subset_sphere_neighborhood
    (hU.inter hV) (subset_inter hSU hSV)
  let S := closedBall (0 : Vector (d + 1)) 1 ∩ {x | r ≤ ‖x‖}
  have hSU' : S ⊆ U := fun x hx ↦ (hS hx).1
  have hSV' : S ⊆ V := fun x hx ↦ (hS hx).2
  have hBP (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ S) :
      (P x).comp (B x) = B x := by
    rw [hBF (hSU' hx.2)]
    apply ContinuousLinearMap.ext
    intro w
    exact projection_apply_range (P x) (hP x hx.1)
      ⟨F x w, hFr x ⟨hx.1, hSV' hx.2⟩ ⟨w, rfl⟩⟩
  have hBn (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ S)
      (w : Vector n) : ‖B x w‖ = ‖w‖ := by
    rw [hBF (hSU' hx.2)]
    exact hFn x ⟨hx.1, hSV' hx.2⟩ w
  have hSc : IsClosed S :=
    isClosed_closedBall.inter (isClosed_le continuous_const continuous_norm)
  have hBs : ContDiffOn ℝ ∞ B U := hFs.contDiffOn.congr hBF
  obtain ⟨T, hTs, hTn, hTr, hT⟩ := exists_smoothPartialFrame_rel
    (isCompact_closedBall (0 : Vector (d + 1)) 1) B B.continuous P hPs hBi hBP hBn
    hSc (hU.mem_nhdsSet.mpr hSU') hBs
  refine ⟨r, hr, hr1, hSV', T, hTs, hTn, hTr, ?_⟩
  intro x hx hxr
  exact (hT ⟨hx, hx, hxr⟩).trans (hBF (hSU' ⟨hx, hxr⟩))

end Wikipedia.HopfProblem.DegreeCollapse.DiskPartialFrame
