import Wikipedia.NoExoticSixSphere.EmbeddedDiskThickening
import Wikipedia.NoExoticSixSphere.ThickeningNormalFrame

/-!
# A framed embedded thickening of a partially framed disk

The transverse frame, positive radius, embedded product map, and full
smooth normal frame are all constructed. The full normal frame restricts
exactly to the prescribed partial frame on the original four-disk core.

This supplies an ambient framed product, not an attached surgery trace. Its
attaching face has not yet been identified with a neighborhood in the original
manifold.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.DiskThickening

open GLOrthonormalization Stiefel

structure FramedProduct {N k : ℕ} (D : Vector 4 → Vector N)
    (T : Vector 4 → Vector k →L[ℝ] Vector N) (q : ℕ := 3) where
  smooth_coreFrame : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x
  norm_coreFrame : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖
  range_coreFrame : ∀ x ∈ closedBall (0 : Vector 4) 1,
    (T x).range ≤ (fderiv ℝ D x).rangeᗮ
  transverse : Vector 4 → Vector q →L[ℝ] Vector N
  radius : ℝ
  radius_pos : 0 < radius
  smooth_transverse : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ transverse x
  norm_transverse : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖transverse x w‖ = ‖w‖
  range_transverse : ∀ x ∈ closedBall (0 : Vector 4) 1,
    (transverse x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ
  embedded : IsClosedEmbedding
    (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) radius ↦
      map D transverse (p.1.val, p.2.val))
  smooth : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) radius,
    ContDiffAt ℝ ∞ (map D transverse) (x, v)
  immersive : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) radius,
    Injective (fderiv ℝ (map D transverse) (x, v))
  normalFrame : Vector 4 × Vector q → Vector k →L[ℝ] Vector N
  normalFrame_smooth : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector q) radius, ContDiffAt ℝ ∞ normalFrame (x, v)
  normalFrame_norm : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector q) radius, ∀ w, ‖normalFrame (x, v) w‖ = ‖w‖
  normalFrame_range : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector q) radius,
      (normalFrame (x, v)).range = (fderiv ℝ (map D transverse) (x, v)).rangeᗮ
  normalFrame_core : ∀ x ∈ closedBall (0 : Vector 4) 1, normalFrame (x, 0) = T x

theorem exists_framedProduct_of_transverse {N k q : ℕ} (D : Vector 4 → Vector N)
    (T : Vector 4 → Vector k →L[ℝ] Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hinj : InjOn D (closedBall (0 : Vector 4) 1))
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ) (hN : k + 4 + q = N)
    (C : Vector 4 → Vector q →L[ℝ] Vector N)
    (hCs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C x)
    (hCn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖C x w‖ = ‖w‖)
    (hCr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ) :
    ∃ A : FramedProduct D T q, A.transverse = C := by
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
  let j : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) ε →
      closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) r :=
    fun p ↦ (p.1, ⟨p.2.val, (closedBall_subset_closedBall hεr) p.2.property⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hji : Injective j := by
    intro p z hpz
    exact Prod.ext (congrArg (fun z : closedBall (0 : Vector 4) 1 ×
        closedBall (0 : Vector q) r ↦ z.1) hpz)
      (Subtype.ext (congrArg (fun z : closedBall (0 : Vector 4) 1 ×
        closedBall (0 : Vector q) r ↦ z.2.val) hpz))
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

theorem nonempty_framedProduct {N k q : ℕ} (D : Vector 4 → Vector N)
    (T : Vector 4 → Vector k →L[ℝ] Vector N)
    (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
    (hinj : InjOn D (closedBall (0 : Vector 4) 1))
    (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1,
      (T x).range ≤ (fderiv ℝ D x).rangeᗮ) (hN : k + 4 + q = N) :
    Nonempty (FramedProduct D T q) := by
  obtain ⟨C, hCs, hCn, hCr⟩ :=
    exists_smoothDiskNormalComplement_of_dimension D hD hiD T hTs hTn hTr hN
  obtain ⟨A, _⟩ := exists_framedProduct_of_transverse D T hD hinj hiD hTs hTn hTr hN
    C hCs hCn hCr
  exact ⟨A⟩

end NoExoticSixSphere.DiskThickening
