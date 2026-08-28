import Wikipedia.NoExoticSixSphere.DiskThickening
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# Extending the core normal frame over a thin product

Project the original core frame into the actual thickening normal spaces and
normalize. Compactness supplies a single positive transverse radius on which
this remains injective. The resulting frame is a full orthonormal normal
frame everywhere on the product and retains the original core values exactly.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.DiskThickening

open GLOrthonormalization Stiefel

theorem exists_normalFrame_product {N k q : ℕ}
    (H : Vector 4 × Vector q → Vector N) (T : Vector 4 → Vector k →L[ℝ] Vector N)
    (r : ℝ) (hr : 0 < r)
    (hHs : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) r,
      ContDiffAt ℝ ∞ H (x, v))
    (hHi : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) r,
      Injective (fderiv ℝ H (x, v)))
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (T x).range = (fderiv ℝ H (x, 0)).rangeᗮ) (hN : k + 4 + q = N) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧
      ∃ R : Vector 4 × Vector q → Vector k →L[ℝ] Vector N,
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) ε,
          ContDiffAt ℝ ∞ R (x, v) ∧ (∀ w, ‖R (x, v) w‖ = ‖w‖) ∧
            (R (x, v)).range = (fderiv ℝ H (x, v)).rangeᗮ) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, R (x, 0) = T x := by
  let J : Vector (4 + q) ≃L[ℝ] (Vector 4 × Vector q) :=
    EuclideanSpace.finAddEquivProd (n := 4) (m := q)
  let A : Vector 4 × Vector q → Vector (4 + q) →L[ℝ] Vector N :=
    fun p ↦ (fderiv ℝ H p).comp J.toContinuousLinearMap
  have hAr (p : Vector 4 × Vector q) : (A p).range = (fderiv ℝ H p).range := by
    change LinearMap.range ((fderiv ℝ H p).toLinearMap.comp J.toLinearEquiv.toLinearMap) = _
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  let P : Vector 4 × Vector q → Vector N →L[ℝ] Vector N :=
    fun p ↦ 1 - gramProjection (A p)
  let B : Vector 4 × Vector q → Vector k →L[ℝ] Vector N :=
    fun p ↦ (P p).comp (T p.1)
  have hz : (0 : Vector q) ∈ closedBall (0 : Vector q) r := by simp [hr.le]
  have hPeq (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (v : Vector q) (hv : v ∈ closedBall (0 : Vector q) r) :
      P (x, v) = (fderiv ℝ H (x, v)).rangeᗮ.starProjection := by
    dsimp only [P]
    have he : (A (x, v)).range.starProjection = (fderiv ℝ H (x, v)).range.starProjection :=
      congrArg (fun W : Submodule ℝ (Vector N) ↦ W.starProjection) (hAr (x, v))
    rw [gramProjection_eq_starProjection _ ((hHi x hx v hv).comp J.injective), he,
      Submodule.starProjection_orthogonal']
  have hPr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (v : Vector q) (hv : v ∈ closedBall (0 : Vector q) r) :
      (P (x, v)).range = (fderiv ℝ H (x, v)).rangeᗮ := by
    rw [hPeq x hx v hv]
    exact (fderiv ℝ H (x, v)).rangeᗮ.range_starProjection
  have hBs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (v : Vector q) (hv : v ∈ closedBall (0 : Vector q) r) :
      ContDiffAt ℝ ∞ B (x, v) := by
    have hPs : ContDiffAt ℝ ∞ P (x, v) :=
      contDiffAt_const.sub
        (contMDiffAt_gramProjection (I := 𝓘(ℝ, Vector 4 × Vector q))
          (((hHs x hx v hv).fderiv_right (by simp)).clm_comp contDiffAt_const).contMDiffAt
          ((hHi x hx v hv).comp J.injective)).contDiffAt
    exact hPs.clm_comp ((hTs x hx).comp (x, v) contDiffAt_fst)
  have hBcore (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) : B (x, 0) = T x := by
    change (P (x, 0)).comp (T x) = T x
    rw [hPeq x hx 0 hz]
    apply ContinuousLinearMap.ext
    intro w
    exact (fderiv ℝ H (x, 0)).rangeᗮ.starProjection_eq_self_iff.mpr
      ((hTr x hx).le ⟨w, rfl⟩)
  let U := interior {p : Vector 4 × Vector q | Injective (B p)}
  have hUcore (x : closedBall (0 : Vector 4) 1) : (x.val, (0 : Vector q)) ∈ U := by
    apply mem_interior_iff_mem_nhds.mpr
    have hi : Injective (B (x.val, 0)) := by
      rw [hBcore x x.property]
      exact Stiefel.injective ⟨T x, hTn x x.property⟩
    exact (hBs x x.property 0 hz).continuousAt
      (ContinuousLinearMap.isOpen_injective.mem_nhds hi)
  have hq : Continuous (fun p : closedBall (0 : Vector 4) 1 × Vector q ↦ (p.1.val, p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  obtain ⟨δ, hδ, hδU⟩ := exists_uniform_closedProductTube
    (isOpen_interior.preimage hq) hUcore
  let ε := min δ r
  have hεr : ε ≤ r := min_le_right _ _
  have hiB (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (v : Vector q) (hv : v ∈ closedBall (0 : Vector q) ε) : Injective (B (x, v)) := by
    apply interior_subset (hδU ⟨x, hx⟩ v ?_)
    have hv' : ‖v‖ ≤ ε := by simpa only [mem_closedBall, dist_zero_right] using hv
    exact hv'.trans (min_le_left _ _)
  let R := Orthonormalization.operator B
  refine ⟨ε, lt_min hδ hr, hεr, R, ?_, ?_⟩
  · intro x hx v hv
    have hvr := (closedBall_subset_closedBall hεr) hv
    have hi := hiB x hx v hv
    refine ⟨Orthonormalization.contDiffAt_operator B (x, v) (hBs x hx v hvr) hi,
      Orthonormalization.operator_norm B (x, v) hi, ?_⟩
    have hRr : (R (x, v)).range ≤ (fderiv ℝ H (x, v)).rangeᗮ := by
      rw [Orthonormalization.operator_range B (x, v) hi, ← hPr x hx v hvr]
      rintro y ⟨w, rfl⟩
      exact ⟨T x w, rfl⟩
    apply Submodule.eq_of_le_of_finrank_eq hRr
    have hiR : Injective (R (x, v)) :=
      Stiefel.injective ⟨R (x, v), Orthonormalization.operator_norm B (x, v) hi⟩
    rw [LinearMap.finrank_range_of_inj hiR, finrank_euclideanSpace_fin]
    have hd := (fderiv ℝ H (x, v)).range.finrank_add_finrank_orthogonal
    rw [LinearMap.finrank_range_of_inj (hHi x hx v hvr), Module.finrank_prod,
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin] at hd
    omega
  · intro x hx
    exact (Orthonormalization.operator_eq_self B (x, 0)
      (by rw [hBcore x hx]; exact hTn x hx)).trans (hBcore x hx)

end NoExoticSixSphere.DiskThickening
