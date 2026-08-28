import Wikipedia.HopfProblem.DegreeCollapseDiskPartialFrameCollar
import Wikipedia.NoExoticSixSphere.SmoothProjection

/-!

# Whole-collar normal-frame agreement for actual low-dimensional disks

Construct the normal projection from the actual disk derivative and
install the prescribed smooth frame on an entire inner annulus. This
retains normality, orthonormality and smoothness on the whole original
closed disk, in each source dimension required by low surgery.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LowDiskNormal

open NoExoticSixSphere GLOrthonormalization Stiefel
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

theorem exists_smooth_frame_collar {d N n : ℕ} (D : Vector (d + 1) → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ D x)
    (hiD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, Injective (fderiv ℝ D x))
    (T : Vector (d + 1) → Vector n →L[ℝ] Vector N)
    (hTs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ)
    (F : C(Vector (d + 1), Vector n →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
    (hFT : ∀ s : NoExoticSixSphere.Sphere d, F s.val = T s.val)
    {V : Set (Vector (d + 1))} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
    (hFn : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ V, ∀ w, ‖F x w‖ = ‖w‖)
    (hFr : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ V,
      (F x).range ≤ (fderiv ℝ D x).rangeᗮ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector (d + 1)) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ T' : Vector (d + 1) → Vector n →L[ℝ] Vector N,
        (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T' x) ∧
        (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T' x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
          (T' x).range ≤ (fderiv ℝ D x).rangeᗮ) ∧
        ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖x‖ → T' x = F x := by
  let P : Vector (d + 1) → Vector N →L[ℝ] Vector N :=
    fun x ↦ 1 - gramProjection (fderiv ℝ D x)
  have hPeq (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      P x = (fderiv ℝ D x).rangeᗮ.starProjection := by
    dsimp only [P]
    rw [gramProjection_eq_starProjection _ (hiD x hx),
      Submodule.starProjection_orthogonal']
  have hPr (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      (P x).range = (fderiv ℝ D x).rangeᗮ := by
    rw [hPeq x hx]
    exact (fderiv ℝ D x).rangeᗮ.range_starProjection
  have hP (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      IsIdempotentElem (P x) := by
    rw [hPeq x hx]
    exact (fderiv ℝ D x).rangeᗮ.isIdempotentElem_starProjection
  have hPs (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      ContDiffAt ℝ ∞ P x :=
    contDiffAt_const.sub
      (contMDiffAt_gramProjection (I := 𝓘(ℝ, Vector (d + 1)))
        ((hD x hx).fderiv_right (by simp)).contMDiffAt (hiD x hx)).contDiffAt
  have hc : Continuous (fun x : Disk (E := Vector (d + 1)) ↦ T x.val) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hTs x.val x.property).continuousAt.comp continuous_subtype_val.continuousAt
  let A : C(Disk (E := Vector (d + 1)), Space N n) :=
    ⟨fun x ↦ ⟨T x.val, hTn x.val x.property⟩, hc.subtype_mk _⟩
  have hAr (x : Disk (E := Vector (d + 1))) : (A x).val.range ≤ (P x.val).range := by
    rw [hPr x.val x.property]
    exact hTr x.val x.property
  have hFr' (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ V) :
      (F x).range ≤ (P x).range := by
    rw [hPr x hx.1]
    exact hFr x hx
  obtain ⟨r, hr, hr1, hrV, T', hT's, hT'n, hT'r, hT'F⟩ :=
    DiskPartialFrame.exists_smooth_frame_collar P hP hPs A hAr F hFs hFT hV hSV hFn hFr'
  refine ⟨r, hr, hr1, hrV, T', hT's, hT'n, ?_, hT'F⟩
  intro x hx
  simpa only [hPr x hx] using hT'r x hx

end Wikipedia.HopfProblem.DegreeCollapse.LowDiskNormal
