import Wikipedia.NoExoticSixSphere.SmoothProjectionDiskFrame
import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates
import Wikipedia.NoExoticSixSphere.SmoothProjection

/-!
# Complementary normal directions on a partially framed four-disk

The given partial frame is normal to the actual disk derivative. The remaining
normal directions form the orthogonal complement of their combined operator.
Its rank is computed from the ambient dimension, and smooth projection transport supplies a
full orthonormal frame over the closed disk. No complementary framing is assumed.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

theorem exists_smoothDiskNormalComplement_of_dimension {N k q : ℕ}
    (D : Vector 4 → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (T : Vector 4 → Vector k →L[ℝ] Vector N)
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ) (hN : k + 4 + q = N) :
    ∃ C : Vector 4 → Vector q →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C x) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖C x w‖ = ‖w‖) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1,
        (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ := by
  let B : Vector 4 → Vector (k + 4) →L[ℝ] Vector N :=
    fun x ↦ OperatorSum.operator (T x) (fderiv ℝ D x)
  have hiB (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) : Injective (B x) :=
    OperatorSum.injective_operator _ _ (Stiefel.injective ⟨T x, hTn x hx⟩) (hiD x hx)
      ((fderiv ℝ D x).range.orthogonal_disjoint.symm.mono_left (hTr x hx))
  have hBs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ContDiffAt ℝ ∞ B x :=
    OperatorSum.contDiffAt_operator (hTs x hx) ((hD x hx).fderiv_right (by simp))
  let P : Vector 4 → Vector N →L[ℝ] Vector N := fun x ↦ 1 - gramProjection (B x)
  have hPeq (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      P x = (B x).rangeᗮ.starProjection := by
    dsimp only [P]
    rw [gramProjection_eq_starProjection _ (hiB x hx),
      Submodule.starProjection_orthogonal']
  have hPr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (P x).range = (B x).rangeᗮ := by
    rw [hPeq x hx]
    exact (B x).rangeᗮ.range_starProjection
  have hP (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      IsIdempotentElem (P x) := by
    rw [hPeq x hx]
    exact (B x).rangeᗮ.isIdempotentElem_starProjection
  have hPs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ContDiffAt ℝ ∞ P x :=
    contDiffAt_const.sub
      (contMDiffAt_gramProjection (I := 𝓘(ℝ, Vector 4))
        (hBs x hx).contMDiffAt (hiB x hx)).contDiffAt
  have hr : Module.finrank ℝ (P 0).range = q := by
    rw [hPr 0 (by simp)]
    have h := (B 0).range.finrank_add_finrank_orthogonal
    rw [LinearMap.finrank_range_of_inj (hiB 0 (by simp)),
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h
    omega
  obtain ⟨C, hCs, hCn, hCr⟩ := exists_smoothProjectionDiskFrame P hP hPs hr
  exact ⟨C, hCs, hCn, fun x hx ↦ (hCr x hx).trans (hPr x hx)⟩

theorem exists_smoothDiskNormalComplement {N k : ℕ}
    (D : Vector 4 → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (T : Vector 4 → Vector k →L[ℝ] Vector N)
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ) (hN : k + 4 + 3 = N) :
    ∃ C : Vector 4 → Vector 3 →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C x) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖C x w‖ = ‖w‖) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1,
        (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ :=
  exists_smoothDiskNormalComplement_of_dimension D hD hiD T hTs hTn hTr hN

end NoExoticSixSphere.Stiefel
