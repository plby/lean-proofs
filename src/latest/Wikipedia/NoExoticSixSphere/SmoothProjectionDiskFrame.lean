import Wikipedia.NoExoticSixSphere.ProjectionDiskFrame
import Wikipedia.NoExoticSixSphere.RelativePartialFrameSmoothing
import Mathlib.Analysis.Complex.Tietze

/-!
# Smooth full frames of projection ranges on an actual closed four-disk

The disk contraction supplies a continuous frame. Extend it to the ambient
space, smooth, project, and normalize. Equality of the actual fiber dimensions
shows that the result spans the whole original projection range. No frame or
trivialization is required as an input.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Topology

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

theorem exists_smoothProjectionDiskFrame {N n : ℕ}
    (P : Vector 4 → Vector N →L[ℝ] Vector N)
    (hP : ∀ x ∈ closedBall (0 : Vector 4) 1, IsIdempotentElem (P x))
    (hPs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ P x)
    (hr : Module.finrank ℝ (P 0).range = n) :
    ∃ T : Vector 4 → Vector n →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range = (P x).range := by
  have hPc : Continuous (fun x : Disk (E := Vector 4) ↦ P x.val) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hPs x x.property).continuousAt.comp continuous_subtype_val.continuousAt
  let Pc : C(Disk (E := Vector 4), Vector N →L[ℝ] Vector N) := ⟨_, hPc⟩
  obtain ⟨A, hAr⟩ := ProjectionDisk.exists_frame Pc (fun x ↦ hP x x.property) hr
  have hAr' (x : Disk (E := Vector 4)) : (A x).val.range = (P x.val).range := hAr x
  let Ac : C(Disk (E := Vector 4), Vector n →L[ℝ] Vector N) :=
    ⟨fun x ↦ (A x).val, continuous_subtype_val.comp A.continuous⟩
  obtain ⟨A₀, hA₀⟩ := Ac.exists_restrict_eq isClosed_closedBall
  have heA (x : Disk (E := Vector 4)) : A₀ x.val = (A x).val :=
    ContinuousMap.congr_fun hA₀ x
  have hPA (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (P x).comp (A₀ x) = A₀ x := by
    rw [heA ⟨x, hx⟩]
    apply ContinuousLinearMap.ext
    intro w
    exact projection_apply_range (P x) (hP x hx)
      ⟨(A ⟨x, hx⟩).val w, (hAr' ⟨x, hx⟩).le ⟨w, rfl⟩⟩
  have hAi (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      Injective ((P x).comp (A₀ x)) := by
    rw [hPA x hx, heA ⟨x, hx⟩]
    exact Stiefel.injective _
  obtain ⟨T, hTs, hTn, hTr, _⟩ := exists_smoothPartialFrame_rel
    (S := ∅) (U := ∅) (isCompact_closedBall (0 : Vector 4) 1)
    A₀ A₀.continuous P hPs hAi
    (by simp) (by simp) isClosed_empty (by simp) (by simp)
  refine ⟨T, hTs, hTn, ?_⟩
  intro x hx
  apply Submodule.eq_of_le_of_finrank_eq (hTr x hx)
  have hi : Injective (T x) := Stiefel.injective ⟨T x, hTn x hx⟩
  rw [LinearMap.finrank_range_of_inj hi, ← hAr' ⟨x, hx⟩,
    LinearMap.finrank_range_of_inj (Stiefel.injective _)]

end NoExoticSixSphere.Stiefel
