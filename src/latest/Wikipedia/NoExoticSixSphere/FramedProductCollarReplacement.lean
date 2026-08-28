import Wikipedia.NoExoticSixSphere.FramedDiskThickening
import Wikipedia.NoExoticSixSphere.SmoothFullDiskCollarFrame
import Wikipedia.NoExoticSixSphere.SmoothOperatorComplement

/-!
# Replacing a product's transverse frame by exact collar data

Smooth the transverse frame relative to a whole collar in the actual
combined-operator complement. Rebuild a thin framed embedded product using
that exact frame, without changing its boundary transverse columns.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.DiskThickening.FramedProduct

open GLOrthonormalization Stiefel

variable {N k q : ℕ} {D : Vector 4 → Vector N}
  {T : Vector 4 → Vector k →L[ℝ] Vector N} (A : FramedProduct D T q)
  (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
  (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
  (F : C(Vector 4, Vector q →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
  (hFC : ∀ s : Sphere 3, F s.val = A.transverse s.val)
  {V : Set (Vector 4)} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
  (hFn : ∀ x ∈ closedBall (0 : Vector 4) 1 ∩ V, ∀ w, ‖F x w‖ = ‖w‖)
  (hFr : ∀ x ∈ closedBall (0 : Vector 4) 1 ∩ V,
    (F x).range ≤ (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ)

include A hD hiD hFs hFC hV hSV hFn hFr

theorem exists_transverseFrame_collar :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector 4) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ C : Vector 4 → Vector q →L[ℝ] Vector N,
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖C x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1,
          (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ → C x = F x := by
  let B : Vector 4 → Vector (k + 4) →L[ℝ] Vector N :=
    fun x ↦ OperatorSum.operator (T x) (fderiv ℝ D x)
  have hBi (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) : Injective (B x) :=
    OperatorSum.injective_operator _ _ (Stiefel.injective ⟨T x, A.norm_coreFrame x hx⟩)
      (hiD x hx) ((fderiv ℝ D x).range.orthogonal_disjoint.symm.mono_left
        (A.range_coreFrame x hx))
  have hBs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ContDiffAt ℝ ∞ B x :=
    OperatorSum.contDiffAt_operator (A.smooth_coreFrame x hx)
      ((hD x hx).fderiv_right (by simp))
  let P := OperatorComplement.projection B
  have hP (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      IsIdempotentElem (P x) := OperatorComplement.idempotent_projection B x (hBi x hx)
  have hPs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ContDiffAt ℝ ∞ P x :=
    OperatorComplement.contDiffAt_projection B x (hBs x hx) (hBi x hx)
  have hPr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (P x).range = (B x).rangeᗮ := OperatorComplement.range_projection B x (hBi x hx)
  have hCr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (A.transverse x).range = (P x).range := (A.range_transverse x hx).trans (hPr x hx).symm
  have hFr' (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ V) :
      (F x).range ≤ (P x).range := by rw [hPr x hx.1]; exact hFr x hx
  obtain ⟨r, hr, hr1, hrV, C, hCs, hCn, hCr', hCF⟩ :=
    exists_smoothFullDiskFrame_collar P hP hPs A.transverse A.smooth_transverse
      A.norm_transverse hCr F hFs hFC hV hSV hFn hFr'
  exact ⟨r, hr, hr1, hrV, C, hCs, hCn,
    fun x hx ↦ (hCr' x hx).trans (hPr x hx), hCF⟩

theorem exists_framedProduct_collar (hinj : InjOn D (closedBall (0 : Vector 4) 1))
    (hN : k + 4 + q = N) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector 4) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ A' : FramedProduct D T q,
        (∀ s : Sphere 3, A'.transverse s.val = A.transverse s.val) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ → A'.transverse x = F x := by
  obtain ⟨r, hr, hr1, hrV, C, hCs, hCn, hCr, hCF⟩ :=
    A.exists_transverseFrame_collar hD hiD F hFs hFC hV hSV hFn hFr
  obtain ⟨A', hAC⟩ := exists_framedProduct_of_transverse D T hD hinj hiD
    A.smooth_coreFrame A.norm_coreFrame A.range_coreFrame hN C hCs hCn hCr
  refine ⟨r, hr, hr1, hrV, A', ?_, ?_⟩
  · intro s
    rw [hAC]
    have hrs : r ≤ ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hr1.le
    exact (hCF s.val (sphere_subset_closedBall s.property) hrs).trans (hFC s)
  · intro x hx hxr
    rw [hAC]
    exact hCF x hx hxr

end NoExoticSixSphere.DiskThickening.FramedProduct
