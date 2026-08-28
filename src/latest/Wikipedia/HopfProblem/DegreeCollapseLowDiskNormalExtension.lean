import Wikipedia.HopfProblem.DegreeCollapseSmoothDiskPartialFrame
import Wikipedia.NoExoticSixSphere.SmoothProjection

/-!

# Prescribed normal frames on actual immersed disks in the connectivity range

The normal projection is constructed from the supplied disk derivative.
Injectivity computes its rank, and the dimension inequality leaves enough
normal complement for the actual sphere frame to extend. Relative smoothing
keeps all boundary columns exactly. This covers the disk dimensions needed
to kill the fundamental group and second homology in dimension seven.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowDiskNormal

open NoExoticSixSphere GLOrthonormalization Stiefel

theorem exists_smooth_extension {d N k : ℕ} (hd : 0 < d) (hk : k + 2 * (d + 1) ≤ N)
    (D : Vector (d + 1) → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ D x)
    (hiD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, Injective (fderiv ℝ D x))
    (a : C(NoExoticSixSphere.Sphere d, Space N k))
    (has : ContMDiff (𝓡 d) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s => (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ D s.val).rangeᗮ) :
    ∃ T : Vector (d + 1) → Vector k →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
        (T x).range ≤ (fderiv ℝ D x).rangeᗮ) ∧
      ∀ s, T s.val = (a s).val := by
  let P : Vector (d + 1) → Vector N →L[ℝ] Vector N :=
    fun x => 1 - gramProjection (fderiv ℝ D x)
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
  have hr : Module.finrank ℝ (P 0).range = (N - ((d + 1) + k)) + k := by
    rw [hPr 0 (by simp)]
    have h := (fderiv ℝ D 0).range.finrank_add_finrank_orthogonal
    rw [LinearMap.finrank_range_of_inj (hiD 0 (by simp)),
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h
    omega
  have haP (s : NoExoticSixSphere.Sphere d) : (a s).val.range ≤ (P s.val).range := by
    rw [hPr s.val (sphere_subset_closedBall s.property)]
    exact ha s
  obtain ⟨T, hTs, hTn, hTr, hTb⟩ :=
    DiskPartialFrame.exists_smooth_projection_extension hd
      (by omega : d < N - ((d + 1) + k)) P hP hPs hr a has haP
  exact ⟨T, hTs, hTn, fun x hx => (hTr x hx).trans_eq (hPr x hx), hTb⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowDiskNormal
