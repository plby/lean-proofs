import Wikipedia.HopfProblem.DegreeCollapseLowCoreProduct
import Wikipedia.HopfProblem.DegreeCollapseLowProductFrame
import Wikipedia.NoExoticSixSphere.SmoothOperatorComplement

/-!

# Full normal-frame replacement on the actual low-dimensional product collar

The actual derivative is reindexed by Euclidean product coordinates before
forming its Gram complement. Relative interpolation installs the prescribed
frame over a whole protected product without changing the map or its normal
spaces. The disk and transverse dimensions are independent.
-/

noncomputable section

open Function
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowDiskThickening

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d N q : ℕ} (H : Vector (d + 1) × Vector q → Vector N)

def productDerivative (p : Vector (d + 1) × Vector q) : Vector ((d + 1) + q) →L[ℝ] Vector N :=
  (fderiv ℝ H p).comp
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d + 1) (m := q)).toContinuousLinearMap

theorem range_productDerivative (p : Vector (d + 1) × Vector q) :
    (productDerivative H p).range = (fderiv ℝ H p).range := by
  change LinearMap.range ((fderiv ℝ H p).toLinearMap.comp
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d + 1) (m := q)).toLinearEquiv.toLinearMap) = _
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

theorem injective_productDerivative (p : Vector (d + 1) × Vector q)
    (hi : Injective (fderiv ℝ H p)) : Injective (productDerivative H p) :=
  hi.comp (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d + 1) (m := q)).injective

def productNormalProjection : Vector (d + 1) × Vector q → Vector N →L[ℝ] Vector N :=
  OperatorComplement.projection (productDerivative H)

theorem range_productNormalProjection (p : Vector (d + 1) × Vector q)
    (hi : Injective (fderiv ℝ H p)) :
    (productNormalProjection H p).range = (fderiv ℝ H p).rangeᗮ := by
  rw [productNormalProjection, OperatorComplement.range_projection _ _
    (injective_productDerivative H p hi), range_productDerivative]

theorem idempotent_productNormalProjection (p : Vector (d + 1) × Vector q)
    (hi : Injective (fderiv ℝ H p)) : IsIdempotentElem (productNormalProjection H p) :=
  OperatorComplement.idempotent_projection _ _ (injective_productDerivative H p hi)

theorem contDiffAt_productNormalProjection (p : Vector (d + 1) × Vector q)
    (hs : ContDiffAt ℝ ∞ H p) (hi : Injective (fderiv ℝ H p)) :
    ContDiffAt ℝ ∞ (productNormalProjection H) p :=
  OperatorComplement.contDiffAt_projection _ _
    ((hs.fderiv_right (by simp)).clm_comp contDiffAt_const)
    (injective_productDerivative H p hi)

end Wikipedia.HopfProblem.DegreeCollapse.LowDiskThickening

noncomputable section

open Set Metric Function
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowDiskThickening.FramedCoreProduct

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d N k q : ℕ} {H : Vector (d + 1) × Vector q → Vector N}
  {T : Vector (d + 1) → Vector k →L[ℝ] Vector N} (B : FramedCoreProduct H T)

theorem exists_normalFrame_collar {S : Set (Vector (d + 1))} (hS : IsCompact S)
    (hSK : S ⊆ closedBall (0 : Vector (d + 1)) 1) (r : ℝ) (hr : 0 < r) (hrB : r ≤ B.radius)
    (F : C(Vector (d + 1) × Vector q, Vector k →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
    (hFA : ∀ x ∈ S, F (x, 0) = B.normalFrame (x, 0))
    (hFn : ∀ p ∈ S ×ˢ closedBall (0 : Vector q) r, ∀ w, ‖F p w‖ = ‖w‖)
    (hFr : ∀ p ∈ S ×ˢ closedBall (0 : Vector q) r, (F p).range ≤ (fderiv ℝ H p).rangeᗮ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ∃ G : Vector (d + 1) × Vector q → Vector k →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ v ∈ closedBall (0 : Vector q) ε,
        ContDiffAt ℝ ∞ G (x, v) ∧ (∀ w, ‖G (x, v) w‖ = ‖w‖) ∧
          (G (x, v)).range = (fderiv ℝ H (x, v)).rangeᗮ) ∧
      EqOn G F (S ×ˢ closedBall (0 : Vector q) ε) := by
  let K := closedBall (0 : Vector (d + 1)) 1 ×ˢ closedBall (0 : Vector q) r
  let P := productNormalProjection H
  have hHi (p : Vector (d + 1) × Vector q) (hp : p ∈ K) : Injective (fderiv ℝ H p) :=
    B.immersive p.1 hp.1 p.2 ((closedBall_subset_closedBall hrB) hp.2)
  have hHs (p : Vector (d + 1) × Vector q) (hp : p ∈ K) : ContDiffAt ℝ ∞ H p :=
    B.smooth p.1 hp.1 p.2 ((closedBall_subset_closedBall hrB) hp.2)
  have hP (p : Vector (d + 1) × Vector q) (hp : p ∈ K) : IsIdempotentElem (P p) :=
    idempotent_productNormalProjection H p (hHi p hp)
  have hPs (p : Vector (d + 1) × Vector q) (hp : p ∈ K) : ContDiffAt ℝ ∞ P p :=
    contDiffAt_productNormalProjection H p (hHs p hp) (hHi p hp)
  have hPr (p : Vector (d + 1) × Vector q) (hp : p ∈ K) :
      (P p).range = (fderiv ℝ H p).rangeᗮ := range_productNormalProjection H p (hHi p hp)
  have hAs (p : Vector (d + 1) × Vector q) (hp : p ∈ K) : ContDiffAt ℝ ∞ B.normalFrame p :=
    B.normalFrame_smooth p.1 hp.1 p.2 ((closedBall_subset_closedBall hrB) hp.2)
  have hAn (p : Vector (d + 1) × Vector q) (hp : p ∈ K) (w : Vector k) :
      ‖B.normalFrame p w‖ = ‖w‖ :=
    B.normalFrame_norm p.1 hp.1 p.2 ((closedBall_subset_closedBall hrB) hp.2) w
  have hAr (p : Vector (d + 1) × Vector q) (hp : p ∈ K) :
      (B.normalFrame p).range = (P p).range :=
    (B.normalFrame_range p.1 hp.1 p.2 ((closedBall_subset_closedBall hrB) hp.2)).trans
      (hPr p hp).symm
  have hFr' (p : Vector (d + 1) × Vector q) (hp : p ∈ S ×ˢ closedBall (0 : Vector q) r) :
      (F p).range ≤ (P p).range := by
    rw [hPr p ⟨hSK hp.1, hp.2⟩]
    exact hFr p hp
  obtain ⟨ε, hε, hεr, G, hGs, hGn, hGr, hGF⟩ := LowProductFrame.exists_smoothProductFrame_collar
    (isCompact_closedBall (0 : Vector (d + 1)) 1) hS hSK r hr P hP hPs
    B.normalFrame hAs hAn hAr F hFs hFA hFn hFr'
  refine ⟨ε, hε, hεr, G, ?_, hGF⟩
  intro x hx v hv
  exact ⟨hGs (x, v) ⟨hx, hv⟩, hGn (x, v) ⟨hx, hv⟩,
    (hGr (x, v) ⟨hx, hv⟩).trans (hPr (x, v) ⟨hx, (closedBall_subset_closedBall hεr) hv⟩)⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowDiskThickening.FramedCoreProduct

