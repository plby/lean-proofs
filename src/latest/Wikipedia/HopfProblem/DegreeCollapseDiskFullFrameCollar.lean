import Wikipedia.HopfProblem.DegreeCollapseDiskPartialFrameCollar

/-!

# Full disk projection frames with exact prescribed collars

Relative smoothing in every disk dimension preserves the actual projection
ranges. Equality of the old and new frame ranks upgrades inclusion to equality,
while every prescribed collar value is retained exactly.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskPartialFrame

open NoExoticSixSphere GLOrthonormalization Stiefel
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

theorem exists_smooth_full_frame_collar {d N n : ℕ}
    (P : Vector (d + 1) → Vector N →L[ℝ] Vector N)
    (hP : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, IsIdempotentElem (P x))
    (hPs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ P x)
    (C : Vector (d + 1) → Vector n →L[ℝ] Vector N)
    (hCs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ C x)
    (hCn : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖C x w‖ = ‖w‖)
    (hCr : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, (C x).range = (P x).range)
    (F : C(Vector (d + 1), Vector n →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
    (hFC : ∀ s : NoExoticSixSphere.Sphere d, F s.val = C s.val)
    {V : Set (Vector (d + 1))} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
    (hFn : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ V, ∀ w, ‖F x w‖ = ‖w‖)
    (hFr : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ V, (F x).range ≤ (P x).range) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector (d + 1)) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ C' : Vector (d + 1) → Vector n →L[ℝ] Vector N,
        (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ C' x) ∧
        (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖C' x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, (C' x).range = (P x).range) ∧
        ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖x‖ → C' x = F x := by
  have hc : Continuous (fun x : Disk (E := Vector (d + 1)) ↦ C x.val) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hCs x.val x.property).continuousAt.comp continuous_subtype_val.continuousAt
  let A : C(Disk (E := Vector (d + 1)), Space N n) :=
    ⟨fun x ↦ ⟨C x.val, hCn x.val x.property⟩, hc.subtype_mk _⟩
  have hAr (x : Disk (E := Vector (d + 1))) : (A x).val.range ≤ (P x.val).range :=
    (hCr x.val x.property).le
  obtain ⟨r, hr, hr1, hrV, C', hC's, hC'n, hC'r, hC'F⟩ :=
    exists_smooth_frame_collar P hP hPs A hAr F hFs hFC hV hSV hFn hFr
  refine ⟨r, hr, hr1, hrV, C', hC's, hC'n, ?_, hC'F⟩
  intro x hx
  apply Submodule.eq_of_le_of_finrank_eq (hC'r x hx)
  rw [← hCr x hx,
    LinearMap.finrank_range_of_inj (Stiefel.injective ⟨C' x, hC'n x hx⟩),
    LinearMap.finrank_range_of_inj (Stiefel.injective ⟨C x, hCn x hx⟩)]

end Wikipedia.HopfProblem.DegreeCollapse.DiskPartialFrame

