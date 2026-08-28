import Wikipedia.HopfProblem.DegreeCollapseFourComplementFrameExtension
import Wikipedia.NoExoticSixSphere.SmoothDiskNormalCollarFrame

/-!
# Smooth prescribed normal frames on an actual immersed four-disk

The projection comes from the disk derivative. Its rank is computed from
injectivity, and four remaining normal directions suffice to extend every
prescribed boundary frame. Compatible smooth collar data can be retained
on an entire annulus. No initial partial-frame extension is supplied.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FourDiskNormal

open NoExoticSixSphere GLOrthonormalization Stiefel

theorem exists_smooth_extension {N k : ℕ} (hk : k + 8 ≤ N)
    (D : Vector 4 → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (a : C(NoExoticSixSphere.Sphere 3, Space N k))
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ D s.val).rangeᗮ) :
    ∃ T : Vector 4 → Vector k →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1,
        (T x).range ≤ (fderiv ℝ D x).rangeᗮ) ∧
      ∀ s, T s.val = (a s).val := by
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
  have hr : Module.finrank ℝ (P 0).range = (N - (4 + k)) + k := by
    rw [hPr 0 (by simp)]
    have h := (fderiv ℝ D 0).range.finrank_add_finrank_orthogonal
    rw [LinearMap.finrank_range_of_inj (hiD 0 (by simp)),
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h
    omega
  have haP (s : NoExoticSixSphere.Sphere 3) : (a s).val.range ≤ (P s.val).range := by
    rw [hPr s.val (sphere_subset_closedBall s.property)]
    exact ha s
  obtain ⟨T, hTs, hTn, hTr, hTb⟩ :=
    FourComplementFrame.exists_smooth_projection_extension
      (by omega : 3 < N - (4 + k)) P hP hPs hr a has haP
  exact ⟨T, hTs, hTn, fun x hx ↦ (hTr x hx).trans_eq (hPr x hx), hTb⟩

theorem exists_smooth_collar_extension {N k : ℕ} (hk : k + 8 ≤ N)
    (D : Vector 4 → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (a : C(NoExoticSixSphere.Sphere 3, Space N k))
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ D s.val).rangeᗮ)
    (F : C(Vector 4, Vector k →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
    (hFa : ∀ s : NoExoticSixSphere.Sphere 3, F s.val = (a s).val)
    {V : Set (Vector 4)} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
    (hFn : ∀ x ∈ closedBall (0 : Vector 4) 1 ∩ V, ∀ w, ‖F x w‖ = ‖w‖)
    (hFr : ∀ x ∈ closedBall (0 : Vector 4) 1 ∩ V,
      (F x).range ≤ (fderiv ℝ D x).rangeᗮ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector 4) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ T : Vector 4 → Vector k →L[ℝ] Vector N,
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1,
          (T x).range ≤ (fderiv ℝ D x).rangeᗮ) ∧
        (∀ s : NoExoticSixSphere.Sphere 3, T s.val = (a s).val) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ → T x = F x := by
  obtain ⟨T₀, hTs, hTn, hTr, hTb⟩ := exists_smooth_extension hk D hD hiD a has ha
  obtain ⟨r, hr, hr1, hrV, T, hT's, hT'n, hT'r, hTF⟩ :=
    exists_smoothDiskNormalFrame_collar D hD hiD T₀ hTs hTn hTr F hFs
      (fun s ↦ (hFa s).trans (hTb s).symm) hV hSV hFn hFr
  refine ⟨r, hr, hr1, hrV, T, hT's, hT'n, hT'r, ?_, hTF⟩
  intro s
  have hrs : r ≤ ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hr1.le
  exact (hTF s.val (sphere_subset_closedBall s.property) hrs).trans (hFa s)

end Wikipedia.HopfProblem.DegreeCollapse.FourDiskNormal
