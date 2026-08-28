import Wikipedia.HopfProblem.DegreeCollapseDiskPartialFrameExtension
import Wikipedia.NoExoticSixSphere.RelativePartialFrameSmoothing
import Mathlib.Analysis.Complex.Tietze

/-!

# Smooth full frames of actual projection ranges on low-dimensional disks

Contraction of the original disk constructs its continuous range frame.
Ambient extension, relative smoothing, projection and orthonormalization
produce a smooth frame. Its exact dimension proves that it spans the
entire original range, without an input trivialization or chosen frame.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskPartialFrame

open NoExoticSixSphere GLOrthonormalization Stiefel
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

theorem exists_smooth_full_frame {d N n : ℕ}
    (P : Vector (d + 1) → Vector N →L[ℝ] Vector N)
    (hP : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, IsIdempotentElem (P x))
    (hPs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ P x)
    (hr : Module.finrank ℝ (P 0).range = n) :
    ∃ T : Vector (d + 1) → Vector n →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, (T x).range = (P x).range := by
  have hPc : Continuous (fun x : Disk (E := Vector (d + 1)) ↦ P x.val) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hPs x x.property).continuousAt.comp continuous_subtype_val.continuousAt
  let Pc : C(Disk (E := Vector (d + 1)), Vector N →L[ℝ] Vector N) := ⟨_, hPc⟩
  obtain ⟨A, hAr⟩ := exists_range_frame Pc (fun x ↦ hP x x.property) hr
  have hAr' (x : Disk (E := Vector (d + 1))) : (A x).val.range = (P x.val).range := hAr x
  let Ac : C(Disk (E := Vector (d + 1)), Vector n →L[ℝ] Vector N) :=
    ⟨fun x ↦ (A x).val, continuous_subtype_val.comp A.continuous⟩
  obtain ⟨A₀, hA₀⟩ := Ac.exists_restrict_eq isClosed_closedBall
  have heA (x : Disk (E := Vector (d + 1))) : A₀ x.val = (A x).val :=
    ContinuousMap.congr_fun hA₀ x
  have hPA (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      (P x).comp (A₀ x) = A₀ x := by
    rw [heA ⟨x, hx⟩]
    apply ContinuousLinearMap.ext
    intro w
    exact projection_apply_range (P x) (hP x hx)
      ⟨(A ⟨x, hx⟩).val w, (hAr' ⟨x, hx⟩).le ⟨w, rfl⟩⟩
  have hAi (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      Injective ((P x).comp (A₀ x)) := by
    rw [hPA x hx, heA ⟨x, hx⟩]
    exact Stiefel.injective _
  obtain ⟨T, hTs, hTn, hTr, _⟩ := exists_smoothPartialFrame_rel
    (S := ∅) (U := ∅) (isCompact_closedBall (0 : Vector (d + 1)) 1)
    A₀ A₀.continuous P hPs hAi
    (by simp) (by simp) isClosed_empty (by simp) (by simp)
  refine ⟨T, hTs, hTn, ?_⟩
  intro x hx
  apply Submodule.eq_of_le_of_finrank_eq (hTr x hx)
  have hi : Injective (T x) := Stiefel.injective ⟨T x, hTn x hx⟩
  rw [LinearMap.finrank_range_of_inj hi, ← hAr' ⟨x, hx⟩,
    LinearMap.finrank_range_of_inj (Stiefel.injective _)]

end Wikipedia.HopfProblem.DegreeCollapse.DiskPartialFrame
