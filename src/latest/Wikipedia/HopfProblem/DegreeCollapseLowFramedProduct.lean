import Wikipedia.HopfProblem.DegreeCollapseLowDiskThickening
import Wikipedia.HopfProblem.DegreeCollapseDiskFullProjectionFrame
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredFramedDisk

/-!

# Actual framed products from the constructed low-dimensional surgery cores

Construct every transverse direction from the actual combined disk derivative
and prescribed normal frame. The affine thickening has a positive embedded
closed product neighborhood and a full smooth normal frame retaining its core
values. For the constructed low-surgery cores, the product dimension is eight.
Agreement with the entire native attaching tube and the trace remains to prove.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowFramedProduct

open NoExoticSixSphere GLOrthonormalization Stiefel LowDiskThickening

theorem exists_transverse_frame {d N k q : ℕ}
    (D : Vector (d + 1) → Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ D x)
    (hiD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, Injective (fderiv ℝ D x))
    (T : Vector (d + 1) → Vector k →L[ℝ] Vector N)
    (hTs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ) (hN : k + (d + 1) + q = N) :
    ∃ C : Vector (d + 1) → Vector q →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ C x) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖C x w‖ = ‖w‖) ∧
      ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
        (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ := by
  let B : Vector (d + 1) → Vector (k + (d + 1)) →L[ℝ] Vector N :=
    fun x ↦ OperatorSum.operator (T x) (fderiv ℝ D x)
  have hiB (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) : Injective (B x) :=
    OperatorSum.injective_operator _ _ (Stiefel.injective ⟨T x, hTn x hx⟩) (hiD x hx)
      ((fderiv ℝ D x).range.orthogonal_disjoint.symm.mono_left (hTr x hx))
  have hBs (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      ContDiffAt ℝ ∞ B x :=
    OperatorSum.contDiffAt_operator (hTs x hx) ((hD x hx).fderiv_right (by simp))
  let P : Vector (d + 1) → Vector N →L[ℝ] Vector N := fun x ↦ 1 - gramProjection (B x)
  have hPeq (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      P x = (B x).rangeᗮ.starProjection := by
    dsimp only [P]
    rw [gramProjection_eq_starProjection _ (hiB x hx),
      Submodule.starProjection_orthogonal']
  have hPr (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      (P x).range = (B x).rangeᗮ := by
    rw [hPeq x hx]
    exact (B x).rangeᗮ.range_starProjection
  have hP (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      IsIdempotentElem (P x) := by
    rw [hPeq x hx]
    exact (B x).rangeᗮ.isIdempotentElem_starProjection
  have hPs (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      ContDiffAt ℝ ∞ P x :=
    contDiffAt_const.sub
      (contMDiffAt_gramProjection (I := 𝓘(ℝ, Vector (d + 1)))
        (hBs x hx).contMDiffAt (hiB x hx)).contDiffAt
  have hr : Module.finrank ℝ (P 0).range = q := by
    rw [hPr 0 (by simp)]
    have h := (B 0).range.finrank_add_finrank_orthogonal
    rw [LinearMap.finrank_range_of_inj (hiB 0 (by simp)),
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h
    omega
  obtain ⟨C, hCs, hCn, hCr⟩ := DiskPartialFrame.exists_smooth_full_frame P hP hPs hr
  exact ⟨C, hCs, hCn, fun x hx ↦ (hCr x hx).trans (hPr x hx)⟩

structure FramedProduct {d N k q : ℕ} (D : Vector (d + 1) → Vector N)
    (T : Vector (d + 1) → Vector k →L[ℝ] Vector N) where
  smooth_coreFrame : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T x
  norm_coreFrame : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T x w‖ = ‖w‖
  range_coreFrame : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
    (T x).range ≤ (fderiv ℝ D x).rangeᗮ
  transverse : Vector (d + 1) → Vector q →L[ℝ] Vector N
  radius : ℝ
  radius_pos : 0 < radius
  smooth_transverse : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ transverse x
  norm_transverse : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖transverse x w‖ = ‖w‖
  range_transverse : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
    (transverse x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ
  embedded : IsClosedEmbedding
    (fun p : closedBall (0 : Vector (d + 1)) 1 × closedBall (0 : Vector q) radius ↦
      map D transverse (p.1.val, p.2.val))
  smooth : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ v ∈ closedBall (0 : Vector q) radius,
    ContDiffAt ℝ ∞ (map D transverse) (x, v)
  immersive : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ v ∈ closedBall (0 : Vector q) radius,
    Injective (fderiv ℝ (map D transverse) (x, v))
  normalFrame : Vector (d + 1) × Vector q → Vector k →L[ℝ] Vector N
  normalFrame_smooth : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
    ∀ v ∈ closedBall (0 : Vector q) radius, ContDiffAt ℝ ∞ normalFrame (x, v)
  normalFrame_norm : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
    ∀ v ∈ closedBall (0 : Vector q) radius, ∀ w, ‖normalFrame (x, v) w‖ = ‖w‖
  normalFrame_range : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
    ∀ v ∈ closedBall (0 : Vector q) radius,
      (normalFrame (x, v)).range = (fderiv ℝ (map D transverse) (x, v)).rangeᗮ
  normalFrame_core : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, normalFrame (x, 0) = T x

theorem exists_framedProduct_of_transverse {d N k q : ℕ} (D : Vector (d + 1) → Vector N)
    (T : Vector (d + 1) → Vector k →L[ℝ] Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ D x)
    (hinj : InjOn D (closedBall (0 : Vector (d + 1)) 1))
    (hiD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, Injective (fderiv ℝ D x))
    (hTs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ) (hN : k + (d + 1) + q = N)
    (C : Vector (d + 1) → Vector q →L[ℝ] Vector N)
    (hCs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ C x)
    (hCn : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖C x w‖ = ‖w‖)
    (hCr : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
      (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ) :
    ∃ A : FramedProduct (q := q) D T, A.transverse = C := by
  have hiC (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) : Injective (C x) :=
    Stiefel.injective ⟨C x, hCn x hx⟩
  have hCD (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      (C x).range ≤ (fderiv ℝ D x).rangeᗮ := by
    rw [hCr x hx, OperatorSum.range_operator, ← Submodule.inf_orthogonal]
    exact inf_le_right
  obtain ⟨r, hr, hemb, hmap⟩ := exists_embedded_product D C hD hCs hinj hiD hiC hCD
  have hcore (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      (T x).range = (fderiv ℝ (map D C) (x, 0)).rangeᗮ :=
    normal_range_core D C T x (hD x hx) (hCs x hx) (hiD x hx)
      (Stiefel.injective ⟨T x, hTn x hx⟩) (hiC x hx) (hTr x hx) (hCr x hx) hN
  obtain ⟨ε, hε, hεr, R, hR, hRcore⟩ := exists_normalFrame_product (map D C) T r hr
    (fun x hx v hv ↦ (hmap x hx v hv).1) (fun x hx v hv ↦ (hmap x hx v hv).2)
    hTs hTn hcore hN
  let j : closedBall (0 : Vector (d + 1)) 1 × closedBall (0 : Vector q) ε →
      closedBall (0 : Vector (d + 1)) 1 × closedBall (0 : Vector q) r :=
    fun p ↦ (p.1, ⟨p.2.val, (closedBall_subset_closedBall hεr) p.2.property⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hji : Injective j := by
    intro p p' hpq
    exact Prod.ext (congrArg (fun z : closedBall (0 : Vector (d + 1)) 1 ×
        closedBall (0 : Vector q) r ↦ z.1) hpq)
      (Subtype.ext (congrArg (fun z : closedBall (0 : Vector (d + 1)) 1 ×
        closedBall (0 : Vector q) r ↦ z.2.val) hpq))
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

theorem nonempty_framedProduct {d N k q : ℕ} (D : Vector (d + 1) → Vector N)
    (T : Vector (d + 1) → Vector k →L[ℝ] Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ D x)
    (hinj : InjOn D (closedBall (0 : Vector (d + 1)) 1))
    (hiD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, Injective (fderiv ℝ D x))
    (hTs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ) (hN : k + (d + 1) + q = N) :
    Nonempty (FramedProduct (q := q) D T) := by
  obtain ⟨C, hCs, hCn, hCr⟩ :=
    exists_transverse_frame D hD hiD T hTs hTn hTr hN
  obtain ⟨A, _⟩ := exists_framedProduct_of_transverse D T hD hinj hiD hTs hTn hTr hN
    C hCs hCn hCr
  exact ⟨A⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowFramedProduct

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.CollaredFramedDisk

open NoExoticSixSphere GLOrthonormalization Stiefel

theorem nonempty_eightDimensionalProduct {d N k : ℕ}
    {b : NoExoticSixSphere.Sphere d} {f : NoExoticSixSphere.Sphere d → Vector N}
    {a : NoExoticSixSphere.Sphere d → Space N k}
    (D : CollaredFramedDisk b f a) (hN : k + 7 = N) (hsmall : d ≤ 3) :
    Nonempty (LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame) := by
  have hinj : InjOn D.map (closedBall (0 : Vector (d + 1)) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val
      (D.embedded.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  exact LowFramedProduct.nonempty_framedProduct D.map D.frame
    (fun _ _ => D.smooth.contDiffAt) hinj D.immersive
    D.frame_smooth D.frame_norm D.frame_normal (by omega)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.CollaredFramedDisk

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel

theorem exists_native_eightDimensionalProduct {d : ℕ} (hd : 0 < d) (hsmall : d ≤ 3)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
    (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : NoExoticSixSphere.Sphere d → M)
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
    (hdf : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s)) :
    ∃ D : CollaredFramedDisk (spherePole d)
        (e.toFun ∘ f) (fun s => a.orthonormal (f s)),
      Nonempty (LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame) := by
  obtain ⟨D⟩ := nonempty_native_collaredFramedDisk hd hsmall e a f hf hi hdf
  have hdim := e.dimension_le_ambient (f (spherePole d))
  exact ⟨D, D.nonempty_eightDimensionalProduct (by omega) hsmall⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
