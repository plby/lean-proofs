import Wikipedia.HopfProblem.DegreeCollapseGeneralDiskThickening
import Wikipedia.NoExoticSixSphere.ClosedProductRestriction

/-!
# General embedded and framed products with the exact original disk core

Compact-core injectivity gives an embedded product for an arbitrary smooth
map. The actual normal projection extends the prescribed full core frame.
A separate compactness theorem gives uniform avoidance of a closed set for
an affine thickening of a compact core. No boundary collar is inferred.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening

open NoExoticSixSphere GLOrthonormalization

theorem restrict_closedProduct_embedding {d : ℕ} {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Y]
    (H : X × Vector d → Y) {r ε : ℝ} (hεr : ε ≤ r)
    (hH : IsClosedEmbedding (fun p : X × closedBall (0 : Vector d) r ↦ H (p.1, p.2.val))) :
    IsClosedEmbedding (fun p : X × closedBall (0 : Vector d) ε ↦ H (p.1, p.2.val)) := by
  let j : X × closedBall (0 : Vector d) ε → X × closedBall (0 : Vector d) r :=
    fun p ↦ (p.1, ⟨p.2.val, (closedBall_subset_closedBall hεr) p.2.property⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hji : Injective j := by
    intro p q hpq
    exact Prod.ext (congrArg (Prod.fst : X × closedBall (0 : Vector d) r → X) hpq)
      (Subtype.ext (congrArg (fun z : X × closedBall (0 : Vector d) r ↦ z.2.val) hpq))
  exact hH.comp (hj.isClosedEmbedding hji)

theorem exists_embedded_core_product {N d : ℕ} (H : Vector 4 × Vector d → Vector N)
    (r : ℝ) (hr : 0 < r)
    (hHs : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector d) r,
      ContDiffAt ℝ ∞ H (x, v))
    (hcore : InjOn (fun x ↦ H (x, 0)) (closedBall (0 : Vector 4) 1))
    (hi : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ H (x, 0))) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧
      IsClosedEmbedding (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector d) ε ↦
        H (p.1.val, p.2.val)) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector d) ε,
        ContDiffAt ℝ ∞ H (x, v) ∧ Injective (fderiv ℝ H (x, v)) := by
  let K := closedBall (0 : Vector 4) 1 ×ˢ ({0} : Set (Vector d))
  have hK : IsCompact K := (isCompact_closedBall (0 : Vector 4) 1).prod isCompact_singleton
  have hKs : ∀ p ∈ K, ContDiffAt ℝ ∞ H p := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact hHs x hx 0 (mem_closedBall_self hr.le)
  have hKi : InjOn H K := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩ ⟨y, w⟩ ⟨hy, hw⟩ he
    rcases mem_singleton_iff.mp hv with rfl
    rcases mem_singleton_iff.mp hw with rfl
    exact Prod.ext (hcore hx hy he) rfl
  have hKd : ∀ p ∈ K, Injective (fderiv ℝ H p) := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact hi x hx
  obtain ⟨V, hV, hKV, hVi, hVd⟩ :=
    CompactCoreImmersion.exists_open_injOn_near_compact hK hKs hKi hKd
  let q : closedBall (0 : Vector 4) 1 × Vector d → Vector 4 × Vector d :=
    fun p ↦ (p.1.val, p.2)
  have hq : Continuous q :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  obtain ⟨δ, hδ, hδV⟩ := exists_uniform_closedProductTube (hV.preimage hq)
    (fun x ↦ hKV ⟨x.property, rfl⟩)
  let ε := min δ r
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεr : ε ≤ r := min_le_right _ _
  have hm (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (v : Vector d) (hv : v ∈ closedBall (0 : Vector d) ε) : (x, v) ∈ V := by
    apply hδV ⟨x, hx⟩ v
    have hvδ := (closedBall_subset_closedBall hεδ) hv
    simpa only [mem_closedBall, dist_zero_right] using hvδ
  let j : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector d) ε → Vector 4 × Vector d :=
    fun p ↦ (p.1.val, p.2.val)
  have hj : Continuous j := (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector d) ε ↦
      H (p.1.val, p.2.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := j)
      (hHs p.1.val p.1.property p.2.val
        ((closedBall_subset_closedBall hεr) p.2.property)).continuousAt hj.continuousAt
  refine ⟨ε, lt_min hδ hr, hεr, hc.isClosedEmbedding ?_, ?_⟩
  · intro p q hpq
    have hp := hVi (hm p.1.val p.1.property p.2.val p.2.property)
      (hm q.1.val q.1.property q.2.val q.2.property) hpq
    exact Prod.ext (Subtype.ext (congrArg (Prod.fst : Vector 4 × Vector d → _) hp))
      (Subtype.ext (congrArg (Prod.snd : Vector 4 × Vector d → _) hp))
  · intro x hx v hv
    exact ⟨hHs x hx v ((closedBall_subset_closedBall hεr) hv), hVd (x, v) (hm x hx v hv)⟩

end Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening

noncomputable section

open Set Metric Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening

open NoExoticSixSphere GLOrthonormalization

theorem exists_avoiding_closed_product {N d : ℕ} {K : Set (Vector 4)} (hK : IsCompact K)
    (D : Vector 4 → Vector N) (C : Vector 4 → Vector d →L[ℝ] Vector N)
    (hD : ∀ x ∈ K, ContDiffAt ℝ ∞ D x) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x)
    {L : Set (Vector N)} (hL : IsClosed L) (havoid : ∀ x ∈ K, D x ∉ L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ v ∈ closedBall (0 : Vector d) ε,
      map D C (x, v) ∉ L := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let j : K × Vector d → Vector 4 × Vector d := fun p ↦ (p.1.val, p.2)
  have hj : Continuous j :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hc : Continuous (fun p : K × Vector d ↦ map D C (p.1.val, p.2)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := j)
      (contDiffAt_map D C p.1.val p.2 (hD p.1.val p.1.property)
        (hC p.1.val p.1.property)).continuousAt hj.continuousAt
  let U := (fun p : K × Vector d ↦ map D C (p.1.val, p.2)) ⁻¹' Lᶜ
  have hU : IsOpen U := hL.isOpen_compl.preimage hc
  have hzero (x : K) : (x, (0 : Vector d)) ∈ U := by
    change map D C (x.val, 0) ∉ L
    rw [map_core]
    exact havoid x.val x.property
  obtain ⟨ε, hε, hεU⟩ := exists_uniform_closedProductTube hU hzero
  refine ⟨ε, hε, ?_⟩
  intro x hx v hv
  exact hεU ⟨x, hx⟩ v (by simpa only [mem_closedBall, dist_zero_right] using hv)

end Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening

open NoExoticSixSphere GLOrthonormalization

structure FramedCoreProduct {N k d : ℕ} (H : Vector 4 × Vector d → Vector N)
    (T : Vector 4 → Vector k →L[ℝ] Vector N) where
  radius : ℝ
  radius_pos : 0 < radius
  embedded : IsClosedEmbedding
    (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector d) radius ↦ H (p.1.val, p.2.val))
  smooth : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector d) radius,
    ContDiffAt ℝ ∞ H (x, v)
  immersive : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector d) radius,
    Injective (fderiv ℝ H (x, v))
  normalFrame : Vector 4 × Vector d → Vector k →L[ℝ] Vector N
  normalFrame_smooth : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector d) radius, ContDiffAt ℝ ∞ normalFrame (x, v)
  normalFrame_norm : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector d) radius, ∀ w, ‖normalFrame (x, v) w‖ = ‖w‖
  normalFrame_range : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector d) radius,
      (normalFrame (x, v)).range = (fderiv ℝ H (x, v)).rangeᗮ
  normalFrame_core : ∀ x ∈ closedBall (0 : Vector 4) 1, normalFrame (x, 0) = T x

theorem exists_framedCoreProduct {N k d : ℕ} (H : Vector 4 × Vector d → Vector N)
    (T : Vector 4 → Vector k →L[ℝ] Vector N) (r : ℝ) (hr : 0 < r)
    (hemb : IsClosedEmbedding
      (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector d) r ↦ H (p.1.val, p.2.val)))
    (hHs : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector d) r,
      ContDiffAt ℝ ∞ H (x, v))
    (hHi : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector d) r,
      Injective (fderiv ℝ H (x, v)))
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range = (fderiv ℝ H (x, 0)).rangeᗮ)
    (hN : k + 4 + d = N) : ∃ B : FramedCoreProduct H T, B.radius ≤ r := by
  obtain ⟨ε, hε, hεr, R, hR, hRcore⟩ :=
    exists_normalFrame_product H T r hr hHs hHi hTs hTn hTr hN
  refine ⟨{
    radius := ε
    radius_pos := hε
    embedded := restrict_closedProduct_embedding
      (fun p : closedBall (0 : Vector 4) 1 × Vector d ↦ H (p.1.val, p.2)) hεr hemb
    smooth := fun x hx v hv ↦ hHs x hx v ((closedBall_subset_closedBall hεr) hv)
    immersive := fun x hx v hv ↦ hHi x hx v ((closedBall_subset_closedBall hεr) hv)
    normalFrame := R
    normalFrame_smooth := fun x hx v hv ↦ (hR x hx v hv).1
    normalFrame_norm := fun x hx v hv ↦ (hR x hx v hv).2.1
    normalFrame_range := fun x hx v hv ↦ (hR x hx v hv).2.2
    normalFrame_core := hRcore }, hεr⟩

end Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskThickening
