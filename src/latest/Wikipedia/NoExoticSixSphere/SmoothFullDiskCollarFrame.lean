import Wikipedia.NoExoticSixSphere.SmoothDiskCollarFrame

/-!
# Full projection frames with a prescribed exact collar

The relative partial-frame construction preserves full rank when the original
frame spans each projection range. Its new frame therefore spans the same
entire range, while agreeing exactly with the prescribed collar data.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Topology

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

theorem exists_smoothFullDiskFrame_collar {N n : ℕ}
    (P : Vector 4 → Vector N →L[ℝ] Vector N)
    (hP : ∀ x ∈ closedBall (0 : Vector 4) 1, IsIdempotentElem (P x))
    (hPs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ P x)
    (C : Vector 4 → Vector n →L[ℝ] Vector N)
    (hCs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C x)
    (hCn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖C x w‖ = ‖w‖)
    (hCr : ∀ x ∈ closedBall (0 : Vector 4) 1, (C x).range = (P x).range)
    (F : C(Vector 4, Vector n →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
    (hFC : ∀ s : NoExoticSixSphere.Sphere 3, F s.val = C s.val)
    {V : Set (Vector 4)} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
    (hFn : ∀ x ∈ closedBall (0 : Vector 4) 1 ∩ V, ∀ w, ‖F x w‖ = ‖w‖)
    (hFr : ∀ x ∈ closedBall (0 : Vector 4) 1 ∩ V, (F x).range ≤ (P x).range) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector 4) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ C' : Vector 4 → Vector n →L[ℝ] Vector N,
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C' x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖C' x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, (C' x).range = (P x).range) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ → C' x = F x := by
  have hc : Continuous (fun x : Disk (E := Vector 4) ↦ C x.val) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hCs x.val x.property).continuousAt.comp continuous_subtype_val.continuousAt
  let A : C(Disk (E := Vector 4), Space N n) :=
    ⟨fun x ↦ ⟨C x.val, hCn x.val x.property⟩, hc.subtype_mk _⟩
  have hAr (x : Disk (E := Vector 4)) : (A x).val.range ≤ (P x.val).range :=
    (hCr x.val x.property).le
  obtain ⟨r, hr, hr1, hrV, C', hC's, hC'n, hC'r, hC'F⟩ :=
    exists_smoothDiskFrame_collar P hP hPs A hAr F hFs hFC hV hSV hFn hFr
  refine ⟨r, hr, hr1, hrV, C', hC's, hC'n, ?_, hC'F⟩
  intro x hx
  apply Submodule.eq_of_le_of_finrank_eq (hC'r x hx)
  rw [← hCr x hx,
    LinearMap.finrank_range_of_inj (Stiefel.injective ⟨C' x, hC'n x hx⟩),
    LinearMap.finrank_range_of_inj (Stiefel.injective ⟨C x, hCn x hx⟩)]

end NoExoticSixSphere.Stiefel
