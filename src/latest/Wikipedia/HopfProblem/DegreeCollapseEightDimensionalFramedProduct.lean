import Wikipedia.HopfProblem.DegreeCollapseGeneralDiskThickening
import Wikipedia.HopfProblem.DegreeCollapseFourDiskNormalExtension

/-!
# An actual framed eight-dimensional product from prescribed boundary data

Four complementary normal directions are constructed, not assumed. The
actual affine thickening of an embedded four-disk has a positive embedded
closed product neighborhood and a full smooth normal frame retaining its
core values. Every prescribed smooth boundary frame extends to such a
product when the ambient dimension is its rank plus eight. This does not
assert agreement with the full attaching neighborhood of a filling.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalFramedProduct

open NoExoticSixSphere GLOrthonormalization Stiefel GeneralDiskThickening

theorem exists_transverse_four_frame {N k : ℕ}
    (D : Vector 4 → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (T : Vector 4 → Vector k →L[ℝ] Vector N)
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ) (hN : k + 4 + 4 = N) :
    ∃ C : Vector 4 → Vector 4 →L[ℝ] Vector N,
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
  have hr : Module.finrank ℝ (P 0).range = 4 := by
    rw [hPr 0 (by simp)]
    have h := (B 0).range.finrank_add_finrank_orthogonal
    rw [LinearMap.finrank_range_of_inj (hiB 0 (by simp)),
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h
    omega
  obtain ⟨C, hCs, hCn, hCr⟩ := exists_smoothProjectionDiskFrame P hP hPs hr
  exact ⟨C, hCs, hCn, fun x hx ↦ (hCr x hx).trans (hPr x hx)⟩

structure FramedProduct {N k : ℕ} (D : Vector 4 → Vector N)
    (T : Vector 4 → Vector k →L[ℝ] Vector N) where
  smooth_coreFrame : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x
  norm_coreFrame : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖
  range_coreFrame : ∀ x ∈ closedBall (0 : Vector 4) 1,
    (T x).range ≤ (fderiv ℝ D x).rangeᗮ
  transverse : Vector 4 → Vector 4 →L[ℝ] Vector N
  radius : ℝ
  radius_pos : 0 < radius
  smooth_transverse : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ transverse x
  norm_transverse : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖transverse x w‖ = ‖w‖
  range_transverse : ∀ x ∈ closedBall (0 : Vector 4) 1,
    (transverse x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ
  embedded : IsClosedEmbedding
    (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector 4) radius ↦
      map D transverse (p.1.val, p.2.val))
  smooth : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) radius,
    ContDiffAt ℝ ∞ (map D transverse) (x, v)
  immersive : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) radius,
    Injective (fderiv ℝ (map D transverse) (x, v))
  normalFrame : Vector 4 × Vector 4 → Vector k →L[ℝ] Vector N
  normalFrame_smooth : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector 4) radius, ContDiffAt ℝ ∞ normalFrame (x, v)
  normalFrame_norm : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector 4) radius, ∀ w, ‖normalFrame (x, v) w‖ = ‖w‖
  normalFrame_range : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector 4) radius,
      (normalFrame (x, v)).range = (fderiv ℝ (map D transverse) (x, v)).rangeᗮ
  normalFrame_core : ∀ x ∈ closedBall (0 : Vector 4) 1, normalFrame (x, 0) = T x

theorem exists_framedProduct_of_transverse {N k : ℕ} (D : Vector 4 → Vector N)
    (T : Vector 4 → Vector k →L[ℝ] Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hinj : InjOn D (closedBall (0 : Vector 4) 1))
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ) (hN : k + 4 + 4 = N)
    (C : Vector 4 → Vector 4 →L[ℝ] Vector N)
    (hCs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C x)
    (hCn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖C x w‖ = ‖w‖)
    (hCr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ) :
    ∃ A : FramedProduct D T, A.transverse = C := by
  have hiC (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) : Injective (C x) :=
    Stiefel.injective ⟨C x, hCn x hx⟩
  have hCD (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (C x).range ≤ (fderiv ℝ D x).rangeᗮ := by
    rw [hCr x hx, OperatorSum.range_operator, ← Submodule.inf_orthogonal]
    exact inf_le_right
  obtain ⟨r, hr, hemb, hmap⟩ := exists_embedded_product D C hD hCs hinj hiD hiC hCD
  have hcore (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (T x).range = (fderiv ℝ (map D C) (x, 0)).rangeᗮ :=
    normal_range_core D C T x (hD x hx) (hCs x hx) (hiD x hx)
      (Stiefel.injective ⟨T x, hTn x hx⟩) (hiC x hx) (hTr x hx) (hCr x hx) hN
  obtain ⟨ε, hε, hεr, R, hR, hRcore⟩ := exists_normalFrame_product (map D C) T r hr
    (fun x hx v hv ↦ (hmap x hx v hv).1) (fun x hx v hv ↦ (hmap x hx v hv).2)
    hTs hTn hcore hN
  let j : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector 4) ε →
      closedBall (0 : Vector 4) 1 × closedBall (0 : Vector 4) r :=
    fun p ↦ (p.1, ⟨p.2.val, (closedBall_subset_closedBall hεr) p.2.property⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hji : Injective j := by
    intro p q hpq
    exact Prod.ext (congrArg (fun z : closedBall (0 : Vector 4) 1 ×
        closedBall (0 : Vector 4) r ↦ z.1) hpq)
      (Subtype.ext (congrArg (fun z : closedBall (0 : Vector 4) 1 ×
        closedBall (0 : Vector 4) r ↦ z.2.val) hpq))
  refine ⟨{
    smooth_coreFrame := hTs
    norm_coreFrame := hTn
    range_coreFrame := hTr
    transverse := C
    radius := ε
    radius_pos := hε
    smooth_transverse := hCs
    norm_transverse := hCn
    range_transverse := hCr
    embedded := hemb.comp (hj.isClosedEmbedding hji)
    smooth := fun x hx v hv ↦ (hmap x hx v ((closedBall_subset_closedBall hεr) hv)).1
    immersive := fun x hx v hv ↦ (hmap x hx v ((closedBall_subset_closedBall hεr) hv)).2
    normalFrame := R
    normalFrame_smooth := fun x hx v hv ↦ (hR x hx v hv).1
    normalFrame_norm := fun x hx v hv ↦ (hR x hx v hv).2.1
    normalFrame_range := fun x hx v hv ↦ (hR x hx v hv).2.2
    normalFrame_core := hRcore }, rfl⟩

theorem nonempty_framedProduct {N k : ℕ} (D : Vector 4 → Vector N)
    (T : Vector 4 → Vector k →L[ℝ] Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hinj : InjOn D (closedBall (0 : Vector 4) 1))
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ) (hN : k + 4 + 4 = N) :
    Nonempty (FramedProduct D T) := by
  obtain ⟨C, hCs, hCn, hCr⟩ :=
    exists_transverse_four_frame D hD hiD T hTs hTn hTr hN
  obtain ⟨A, _⟩ := exists_framedProduct_of_transverse D T hD hinj hiD hTs hTn hTr hN
    C hCs hCn hCr
  exact ⟨A⟩

theorem exists_framedProduct_of_boundary {N k : ℕ} (hN : k + 8 = N)
    (D : Vector 4 → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hinj : InjOn D (closedBall (0 : Vector 4) 1))
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (a : C(NoExoticSixSphere.Sphere 3, Space N k))
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ D s.val).rangeᗮ) :
    ∃ T : Vector 4 → Vector k →L[ℝ] Vector N,
      ∃ A : FramedProduct D T,
        ∀ s : NoExoticSixSphere.Sphere 3, A.normalFrame (s.val, 0) = (a s).val := by
  obtain ⟨T, hTs, hTn, hTr, hTb⟩ :=
    FourDiskNormal.exists_smooth_extension hN.le D hD hiD a has ha
  obtain ⟨A⟩ := nonempty_framedProduct D T hD hinj hiD hTs hTn hTr (by omega)
  refine ⟨T, A, ?_⟩
  intro s
  exact (A.normalFrame_core s.val (sphere_subset_closedBall s.property)).trans (hTb s)

theorem exists_framedProduct_of_collar {N k : ℕ} (hN : k + 8 = N)
    (D : Vector 4 → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hinj : InjOn D (closedBall (0 : Vector 4) 1))
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
        ∃ A : FramedProduct D T,
          (∀ s : NoExoticSixSphere.Sphere 3, A.normalFrame (s.val, 0) = (a s).val) ∧
          ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ → A.normalFrame (x, 0) = F x := by
  obtain ⟨r, hr, hr1, hrV, T, hTs, hTn, hTr, hTb, hTF⟩ :=
    FourDiskNormal.exists_smooth_collar_extension hN.le D hD hiD a has ha
      F hFs hFa hV hSV hFn hFr
  obtain ⟨A⟩ := nonempty_framedProduct D T hD hinj hiD hTs hTn hTr (by omega)
  refine ⟨r, hr, hr1, hrV, T, A, ?_, ?_⟩
  · intro s
    exact (A.normalFrame_core s.val (sphere_subset_closedBall s.property)).trans (hTb s)
  · intro x hx hxr
    exact (A.normalFrame_core x hx).trans (hTF x hx hxr)

end Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalFramedProduct
