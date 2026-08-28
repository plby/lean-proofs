import Wikipedia.NoExoticSixSphere.SmoothDiskNormalComplement
import Wikipedia.NoExoticSixSphere.CompactCoreImmersion
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# Actual four-disk thickening with any number of transverse coordinates

Generalize the checked affine thickening and its normal projection from
three transverse directions to an arbitrary number. The map, derivative,
embedded closed product, and full smooth normal frame are the actual
geometric objects; the core frame is retained exactly. Four transverse
directions will give the eight-dimensional product for interior surgery
on a seven-dimensional filling. No filling or attaching-face match is
asserted by these local constructions.
-/

noncomputable section

open Function
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {N k q : ℕ} (D : Vector 4 → Vector N) (C : Vector 4 → Vector q →L[ℝ] Vector N)

def map (p : Vector 4 × Vector q) : Vector N := D p.1 + C p.1 p.2

theorem map_core (x : Vector 4) : map D C (x, 0) = D x := by simp [map]

theorem contDiffAt_map (x : Vector 4) (v : Vector q)
    (hD : ContDiffAt ℝ ∞ D x) (hC : ContDiffAt ℝ ∞ C x) :
    ContDiffAt ℝ ∞ (map D C) (x, v) :=
  (hD.comp (x, v) contDiffAt_fst).add
    ((hC.comp (x, v) contDiffAt_fst).clm_apply contDiffAt_snd)

theorem fderiv_map_core (x : Vector 4)
    (hD : ContDiffAt ℝ ∞ D x) (hC : ContDiffAt ℝ ∞ C x) :
    fderiv ℝ (map D C) (x, 0) = (fderiv ℝ D x).coprod (C x) := by
  have hfst : HasFDerivAt (Prod.fst : Vector 4 × Vector q → Vector 4)
      (ContinuousLinearMap.fst ℝ _ _) (x, 0) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : Vector 4 × Vector q → Vector q)
      (ContinuousLinearMap.snd ℝ _ _) (x, 0) := hasFDerivAt_snd
  have hD' := (hD.differentiableAt (by simp)).hasFDerivAt.comp (x, (0 : Vector q)) hfst
  have hC' := (hC.differentiableAt (by simp)).hasFDerivAt.comp (x, (0 : Vector q)) hfst
  have h := hD'.add (hC'.clm_apply hsnd)
  have hh := h.fderiv
  change fderiv ℝ (map D C) (x, 0) = _ at hh
  rw [hh]
  apply ContinuousLinearMap.ext
  intro p
  change fderiv ℝ D x p.1 + (C x p.2 + fderiv ℝ C x p.1 0) =
    fderiv ℝ D x p.1 + C x p.2
  rw [map_zero, add_zero]

theorem injective_fderiv_map_core (x : Vector 4)
    (hD : ContDiffAt ℝ ∞ D x) (hC : ContDiffAt ℝ ∞ C x)
    (hiD : Injective (fderiv ℝ D x)) (hiC : Injective (C x))
    (hCr : (C x).range ≤ (fderiv ℝ D x).rangeᗮ) :
    Injective (fderiv ℝ (map D C) (x, 0)) := by
  rw [fderiv_map_core D C x hD hC]
  change Injective ((fderiv ℝ D x).toLinearMap.coprod (C x).toLinearMap)
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_coprod_of_disjoint_range _ _
    ((fderiv ℝ D x).range.orthogonal_disjoint.mono_right hCr),
    LinearMap.ker_eq_bot.mpr hiD, LinearMap.ker_eq_bot.mpr hiC, Submodule.prod_bot]

theorem normal_range_core (T : Vector 4 → Vector k →L[ℝ] Vector N) (x : Vector 4)
    (hD : ContDiffAt ℝ ∞ D x) (hC : ContDiffAt ℝ ∞ C x)
    (hiD : Injective (fderiv ℝ D x)) (hiT : Injective (T x)) (hiC : Injective (C x))
    (hTr : (T x).range ≤ (fderiv ℝ D x).rangeᗮ)
    (hCr : (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ)
    (hN : k + 4 + q = N) :
    (T x).range = (fderiv ℝ (map D C) (x, 0)).rangeᗮ := by
  have hCr' : (C x).range = (T x).rangeᗮ ⊓ (fderiv ℝ D x).rangeᗮ := by
    rw [hCr, OperatorSum.range_operator, Submodule.inf_orthogonal]
  have hCD : (C x).range ≤ (fderiv ℝ D x).rangeᗮ := hCr'.le.trans inf_le_right
  have hCT : (C x).range ≤ (T x).rangeᗮ := hCr'.le.trans inf_le_left
  have hTC : (T x).range ≤ (C x).rangeᗮ :=
    (T x).range.le_orthogonal_orthogonal.trans (Submodule.orthogonal_le hCT)
  have hle : (T x).range ≤ (fderiv ℝ (map D C) (x, 0)).rangeᗮ := by
    rw [fderiv_map_core D C x hD hC]
    change (T x).range ≤ ((fderiv ℝ D x).toLinearMap.coprod (C x).toLinearMap).rangeᗮ
    rw [LinearMap.range_coprod, ← Submodule.inf_orthogonal]
    exact le_inf hTr hTC
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj hiT, finrank_euclideanSpace_fin]
  have hd := (fderiv ℝ (map D C) (x, 0)).range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj (injective_fderiv_map_core D C x hD hC hiD hiC hCD),
    Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin] at hd
  omega

end Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening

open NoExoticSixSphere GLOrthonormalization

theorem exists_embedded_product {N q : ℕ} (D : Vector 4 → Vector N)
    (C : Vector 4 → Vector q →L[ℝ] Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hC : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C x)
    (hinj : InjOn D (closedBall (0 : Vector 4) 1))
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (hiC : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (C x))
    (hCr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (C x).range ≤ (fderiv ℝ D x).rangeᗮ) :
    ∃ ε : ℝ, 0 < ε ∧
      IsClosedEmbedding (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) ε ↦
        map D C (p.1.val, p.2.val)) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) ε,
        ContDiffAt ℝ ∞ (map D C) (x, v) ∧ Injective (fderiv ℝ (map D C) (x, v)) := by
  let K := closedBall (0 : Vector 4) 1 ×ˢ ({0} : Set (Vector q))
  have hK : IsCompact K := (isCompact_closedBall (0 : Vector 4) 1).prod isCompact_singleton
  have hHs : ∀ p ∈ K, ContDiffAt ℝ ∞ (map D C) p :=
    fun p hp ↦ contDiffAt_map D C p.1 p.2 (hD p.1 hp.1) (hC p.1 hp.1)
  have hHi : InjOn (map D C) K := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩ ⟨y, w⟩ ⟨hy, hw⟩ he
    rcases mem_singleton_iff.mp hv with rfl
    rcases mem_singleton_iff.mp hw with rfl
    exact Prod.ext (hinj hx hy (by simpa only [map_core] using he)) rfl
  have hHd : ∀ p ∈ K, Injective (fderiv ℝ (map D C) p) := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact injective_fderiv_map_core D C x (hD x hx) (hC x hx)
      (hiD x hx) (hiC x hx) (hCr x hx)
  obtain ⟨V, hV, hKV, hVi, hVd⟩ :=
    CompactCoreImmersion.exists_open_injOn_near_compact hK hHs hHi hHd
  let coreInclusion : closedBall (0 : Vector 4) 1 × Vector q → Vector 4 × Vector q :=
    fun p ↦ (p.1.val, p.2)
  have hq : Continuous coreInclusion :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  obtain ⟨ε, hε, hεV⟩ := exists_uniform_closedProductTube (hV.preimage hq)
    (fun x ↦ hKV ⟨x.property, rfl⟩)
  have hm (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (v : Vector q) (hv : v ∈ closedBall (0 : Vector q) ε) : (x, v) ∈ V := by
    apply hεV ⟨x, hx⟩ v
    simpa only [mem_closedBall, dist_zero_right] using hv
  let j : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) ε → Vector 4 × Vector q :=
    fun p ↦ (p.1.val, p.2.val)
  have hj : Continuous j := (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) ε ↦
      map D C (p.1.val, p.2.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := j)
      (contDiffAt_map D C p.1.val p.2.val (hD p.1 p.1.property)
        (hC p.1 p.1.property)).continuousAt hj.continuousAt
  refine ⟨ε, hε, hc.isClosedEmbedding ?_, ?_⟩
  · intro p q hpq
    have h := hVi (hm p.1 p.1.property p.2 p.2.property)
      (hm q.1 q.1.property q.2 q.2.property) hpq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  · intro x hx v hv
    exact ⟨contDiffAt_map D C x v (hD x hx) (hC x hx), hVd (x, v) (hm x hx v hv)⟩

end Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening

open NoExoticSixSphere GLOrthonormalization Stiefel

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

end Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening
