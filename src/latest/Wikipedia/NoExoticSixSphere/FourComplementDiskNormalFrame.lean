import Wikipedia.NoExoticSixSphere.FourComplementFrameExtension
import Wikipedia.NoExoticSixSphere.DiskNormalProjection
import Wikipedia.NoExoticSixSphere.SmoothDiskFrameExtension

/-!
# Smooth normal-frame extension on an actual immersed four-disk

When the prescribed normal columns leave at least four complementary
normal directions, the exact boundary frame always extends. The normal
spaces and their smooth projections come from the actual disk derivative.
Native connectivity constructs the continuous extension and relative
frame smoothing retains its exact original boundary values.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

namespace DiskNormal

theorem exists_partialFrame_extension_of_complement {N c n : ℕ} (hc : 3 < c)
    (D : C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector N))
    (hi : ∀ x, Injective (D x)) (hN : N = 4 + (c + n))
    (a : C(NoExoticSixSphere.Sphere 3, Space N n))
    (ha : ∀ s, (a s).val.range ≤ (D (boundaryToDisk s)).rangeᗮ) :
    ∃ A : C(Disk (E := Vector 4), Space N n),
      (∀ x, (A x).val.range ≤ (D x).rangeᗮ) ∧ ∀ s, A (boundaryToDisk s) = a s := by
  have hr : Module.finrank ℝ (projectionMap D hi ProjectionDisk.center).range = c + n := by
    have h := finrank_normal D hi ProjectionDisk.center
    omega
  have har (s : NoExoticSixSphere.Sphere 3) :
      (a s).val.range ≤ (projectionMap D hi (boundaryToDisk s)).range := by
    rw [projectionMap_range]
    exact ha s
  obtain ⟨A, hAr, hAb⟩ := ProjectionDisk.exists_partialFrame_extension_of_complement hc
    (projectionMap D hi) (projectionMap_idempotent D hi) hr a har
  exact ⟨A, fun x ↦ by simpa only [projectionMap_range] using hAr x, hAb⟩

end DiskNormal

theorem exists_smoothDiskNormalFrame_of_complement {N c n : ℕ} (hc : 3 < c)
    (f : Vector 4 → Vector N)
    (hf : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ f x)
    (hi : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ f x))
    (hN : N = 4 + (c + n))
    (a : C(NoExoticSixSphere.Sphere 3, Space N n))
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector n →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ f s.val).rangeᗮ) :
    ∃ T : Vector 4 → Vector n →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range ≤ (fderiv ℝ f x).rangeᗮ) ∧
      ∀ s, T s.val = (a s).val := by
  let D : C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector N) := {
    toFun x := fderiv ℝ f x.val
    continuous_toFun := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact ((hf x.val x.property).continuousAt_fderiv (by simp)).comp
        continuous_subtype_val.continuousAt }
  obtain ⟨A, hAr, hAb⟩ := DiskNormal.exists_partialFrame_extension_of_complement hc
    D (fun x ↦ hi x.val x.property) hN a ha
  let P : Vector 4 → Vector N →L[ℝ] Vector N := fun x ↦ 1 - gramProjection (fderiv ℝ f x)
  have hPeq (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      P x = (fderiv ℝ f x).rangeᗮ.starProjection := by
    dsimp only [P]
    rw [gramProjection_eq_starProjection _ (hi x hx), Submodule.starProjection_orthogonal']
  have hPr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (P x).range = (fderiv ℝ f x).rangeᗮ := by
    rw [hPeq x hx]
    exact (fderiv ℝ f x).rangeᗮ.range_starProjection
  have hP (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) : IsIdempotentElem (P x) := by
    rw [hPeq x hx]
    exact (fderiv ℝ f x).rangeᗮ.isIdempotentElem_starProjection
  have hPs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) : ContDiffAt ℝ ∞ P x :=
    contDiffAt_const.sub
      (contMDiffAt_gramProjection (I := 𝓘(ℝ, Vector 4))
        ((hf x hx).fderiv_right (by simp)).contMDiffAt (hi x hx)).contDiffAt
  have hAP (x : Disk (E := Vector 4)) : (A x).val.range ≤ (P x.val).range := by
    rw [hPr x.val x.property]
    exact hAr x
  obtain ⟨T, hTs, hTn, hTr, hTb⟩ := exists_smoothDiskFrame_extension P hP hPs a has A hAP hAb
  exact ⟨T, hTs, hTn, fun x hx ↦ (hTr x hx).trans_eq (hPr x hx), hTb⟩

end NoExoticSixSphere.Stiefel
