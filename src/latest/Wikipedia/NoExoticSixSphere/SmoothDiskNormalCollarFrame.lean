import Wikipedia.NoExoticSixSphere.SmoothDiskCollarFrame
import Wikipedia.NoExoticSixSphere.SmoothProjection

/-!
# Installing an exact smooth collar in a disk's actual normal frame

Starting from a smooth partial normal frame on an immersed four-disk, replace
it by one agreeing with prescribed compatible collar data on a whole annulus.
The projection is constructed from the disk derivative itself. Smoothness,
orthonormality, and normality on the entire closed disk are retained.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

theorem exists_smoothDiskNormalFrame_collar {N n : ℕ} (D : Vector 4 → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (T : Vector 4 → Vector n →L[ℝ] Vector N)
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ)
    (F : C(Vector 4, Vector n →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
    (hFT : ∀ s : NoExoticSixSphere.Sphere 3, F s.val = T s.val)
    {V : Set (Vector 4)} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
    (hFn : ∀ x ∈ closedBall (0 : Vector 4) 1 ∩ V, ∀ w, ‖F x w‖ = ‖w‖)
    (hFr : ∀ x ∈ closedBall (0 : Vector 4) 1 ∩ V,
      (F x).range ≤ (fderiv ℝ D x).rangeᗮ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector 4) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ T' : Vector 4 → Vector n →L[ℝ] Vector N,
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T' x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T' x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1,
          (T' x).range ≤ (fderiv ℝ D x).rangeᗮ) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ → T' x = F x := by
  let P : Vector 4 → Vector N →L[ℝ] Vector N :=
    fun x ↦ 1 - gramProjection (fderiv ℝ D x)
  have hPeq (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      P x = (fderiv ℝ D x).rangeᗮ.starProjection := by
    dsimp only [P]
    rw [gramProjection_eq_starProjection _ (hiD x hx),
      Submodule.starProjection_orthogonal']
  have hPr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (P x).range = (fderiv ℝ D x).rangeᗮ := by
    rw [hPeq x hx]
    exact (fderiv ℝ D x).rangeᗮ.range_starProjection
  have hP (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      IsIdempotentElem (P x) := by
    rw [hPeq x hx]
    exact (fderiv ℝ D x).rangeᗮ.isIdempotentElem_starProjection
  have hPs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ContDiffAt ℝ ∞ P x :=
    contDiffAt_const.sub
      (contMDiffAt_gramProjection (I := 𝓘(ℝ, Vector 4))
        ((hD x hx).fderiv_right (by simp)).contMDiffAt (hiD x hx)).contDiffAt
  have hc : Continuous (fun x : Disk (E := Vector 4) ↦ T x.val) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hTs x.val x.property).continuousAt.comp continuous_subtype_val.continuousAt
  let A : C(Disk (E := Vector 4), Space N n) :=
    ⟨fun x ↦ ⟨T x.val, hTn x.val x.property⟩, hc.subtype_mk _⟩
  have hAr (x : Disk (E := Vector 4)) : (A x).val.range ≤ (P x.val).range := by
    rw [hPr x.val x.property]
    exact hTr x.val x.property
  have hFr' (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ V) :
      (F x).range ≤ (P x).range := by
    rw [hPr x hx.1]
    exact hFr x hx
  obtain ⟨r, hr, hr1, hrV, T', hT's, hT'n, hT'r, hT'F⟩ :=
    exists_smoothDiskFrame_collar P hP hPs A hAr F hFs hFT hV hSV hFn hFr'
  refine ⟨r, hr, hr1, hrV, T', hT's, hT'n, ?_, hT'F⟩
  intro x hx
  simpa only [hPr x hx] using hT'r x hx

end NoExoticSixSphere.Stiefel
