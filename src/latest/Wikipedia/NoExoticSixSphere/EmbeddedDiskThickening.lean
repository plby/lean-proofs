import Wikipedia.NoExoticSixSphere.DiskThickening
import Wikipedia.NoExoticSixSphere.CompactCoreImmersion
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# An embedded product neighborhood of an actual four-disk

A smooth finite-dimensional normal frame gives a thickening of the disk. The original
closed disk is embedded and its thickening derivative is injective along
the core. Compactness supplies one positive transverse radius for which the
whole closed product is embedded and immersive. The map is the actual affine
normal thickening, not a separately chosen model handle.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.DiskThickening

open GLOrthonormalization

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
  · intro p z hpz
    have h := hVi (hm p.1 p.1.property p.2 p.2.property)
      (hm z.1 z.1.property z.2 z.2.property) hpz
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  · intro x hx v hv
    exact ⟨contDiffAt_map D C x v (hD x hx) (hC x hx), hVd (x, v) (hm x hx v hv)⟩

end NoExoticSixSphere.DiskThickening
