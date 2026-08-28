import Wikipedia.NoExoticSixSphere.FramedCoreProduct
import Wikipedia.NoExoticSixSphere.ProductNormalProjection
import Wikipedia.NoExoticSixSphere.RelativeProductFrame

/-!
# Replacing an actual product's full normal frame on a protected collar

The original full normal frame and the prescribed frame agree along a
compact part of the zero section. The actual derivative-normal projections
then give a smooth full frame agreeing with the prescribed family over a
whole thin product there. The product map itself is unchanged.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff

namespace NoExoticSixSphere.DiskThickening.FramedCoreProduct

open GLOrthonormalization Stiefel

variable {N k d : ℕ} {H : Vector 4 × Vector d → Vector N}
  {T : Vector 4 → Vector k →L[ℝ] Vector N} (B : FramedCoreProduct H T)

theorem exists_normalFrame_collar {S : Set (Vector 4)} (hS : IsCompact S)
    (hSK : S ⊆ closedBall (0 : Vector 4) 1) (r : ℝ) (hr : 0 < r) (hrB : r ≤ B.radius)
    (F : C(Vector 4 × Vector d, Vector k →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
    (hFA : ∀ x ∈ S, F (x, 0) = B.normalFrame (x, 0))
    (hFn : ∀ p ∈ S ×ˢ closedBall (0 : Vector d) r, ∀ w, ‖F p w‖ = ‖w‖)
    (hFr : ∀ p ∈ S ×ˢ closedBall (0 : Vector d) r, (F p).range ≤ (fderiv ℝ H p).rangeᗮ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ∃ G : Vector 4 × Vector d → Vector k →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector d) ε,
        ContDiffAt ℝ ∞ G (x, v) ∧ (∀ w, ‖G (x, v) w‖ = ‖w‖) ∧
          (G (x, v)).range = (fderiv ℝ H (x, v)).rangeᗮ) ∧
      EqOn G F (S ×ˢ closedBall (0 : Vector d) ε) := by
  let K := closedBall (0 : Vector 4) 1 ×ˢ closedBall (0 : Vector d) r
  let P := productNormalProjection H
  have hHi (p : Vector 4 × Vector d) (hp : p ∈ K) : Injective (fderiv ℝ H p) :=
    B.immersive p.1 hp.1 p.2 ((closedBall_subset_closedBall hrB) hp.2)
  have hHs (p : Vector 4 × Vector d) (hp : p ∈ K) : ContDiffAt ℝ ∞ H p :=
    B.smooth p.1 hp.1 p.2 ((closedBall_subset_closedBall hrB) hp.2)
  have hP (p : Vector 4 × Vector d) (hp : p ∈ K) : IsIdempotentElem (P p) :=
    idempotent_productNormalProjection H p (hHi p hp)
  have hPs (p : Vector 4 × Vector d) (hp : p ∈ K) : ContDiffAt ℝ ∞ P p :=
    contDiffAt_productNormalProjection H p (hHs p hp) (hHi p hp)
  have hPr (p : Vector 4 × Vector d) (hp : p ∈ K) :
      (P p).range = (fderiv ℝ H p).rangeᗮ := range_productNormalProjection H p (hHi p hp)
  have hAs (p : Vector 4 × Vector d) (hp : p ∈ K) : ContDiffAt ℝ ∞ B.normalFrame p :=
    B.normalFrame_smooth p.1 hp.1 p.2 ((closedBall_subset_closedBall hrB) hp.2)
  have hAn (p : Vector 4 × Vector d) (hp : p ∈ K) (w : Vector k) :
      ‖B.normalFrame p w‖ = ‖w‖ :=
    B.normalFrame_norm p.1 hp.1 p.2 ((closedBall_subset_closedBall hrB) hp.2) w
  have hAr (p : Vector 4 × Vector d) (hp : p ∈ K) :
      (B.normalFrame p).range = (P p).range :=
    (B.normalFrame_range p.1 hp.1 p.2 ((closedBall_subset_closedBall hrB) hp.2)).trans
      (hPr p hp).symm
  have hFr' (p : Vector 4 × Vector d) (hp : p ∈ S ×ˢ closedBall (0 : Vector d) r) :
      (F p).range ≤ (P p).range := by
    rw [hPr p ⟨hSK hp.1, hp.2⟩]
    exact hFr p hp
  obtain ⟨ε, hε, hεr, G, hGs, hGn, hGr, hGF⟩ := exists_smoothProductFrame_collar
    (isCompact_closedBall (0 : Vector 4) 1) hS hSK r hr P hP hPs
    B.normalFrame hAs hAn hAr F hFs hFA hFn hFr'
  refine ⟨ε, hε, hεr, G, ?_, hGF⟩
  intro x hx v hv
  exact ⟨hGs (x, v) ⟨hx, hv⟩, hGn (x, v) ⟨hx, hv⟩,
    (hGr (x, v) ⟨hx, hv⟩).trans (hPr (x, v) ⟨hx, (closedBall_subset_closedBall hεr) hv⟩)⟩

end NoExoticSixSphere.DiskThickening.FramedCoreProduct
