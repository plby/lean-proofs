import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Constructions.SumProd

/-!
# Collapse along an open product embedding with compact base

For an open embedding `τ : M × K → Y`, retain the `K` coordinate on its
image and send the complement to infinity. Compactness of `M` proves
continuity at the collapsed complement, using the one-point topology.
-/

open Set Topology
open scoped OnePoint

namespace NoExoticSixSphere.OpenFiberCollapse

variable {M K Y : Type*} (τ : M × K → Y)

noncomputable def collapse (y : Y) : OnePoint K := by
  classical
  exact if hy : y ∈ range τ then ((Classical.choose hy).2 : OnePoint K) else ∞

theorem collapse_apply (hτ : Function.Injective τ) (p : M × K) :
    collapse τ (τ p) = (p.2 : OnePoint K) := by
  classical
  have hp : τ p ∈ range τ := ⟨p, rfl⟩
  rw [collapse, dif_pos hp]
  exact congrArg (fun q : M × K ↦ (q.2 : OnePoint K))
    (hτ (Classical.choose_spec hp))

theorem collapse_of_not_mem {y : Y} (hy : y ∉ range τ) : collapse τ y = ∞ := by
  classical
  rw [collapse, dif_neg hy]

theorem preimage_eq_image (hτ : Function.Injective τ) {U : Set (OnePoint K)}
    (hU : ∞ ∉ U) :
    collapse τ ⁻¹' U = τ '' (univ ×ˢ (((↑) : K → OnePoint K) ⁻¹' U)) := by
  classical
  ext y
  constructor
  · intro hyU
    by_cases hy : y ∈ range τ
    · refine ⟨Classical.choose hy, ⟨mem_univ _, ?_⟩, Classical.choose_spec hy⟩
      simpa only [mem_preimage, collapse, dif_pos hy] using hyU
    · exact (hU (by simpa only [mem_preimage, collapse_of_not_mem τ hy] using hyU)).elim
  · rintro ⟨p, hp, rfl⟩
    change collapse τ (τ p) ∈ U
    rw [collapse_apply τ hτ]
    exact hp.2

theorem continuous_collapse [TopologicalSpace M] [TopologicalSpace K] [TopologicalSpace Y]
    [CompactSpace M] [T2Space Y]
    (hτ : IsOpenEmbedding τ) : Continuous (collapse τ) := by
  rw [continuous_def]
  intro U hU
  by_cases hinfty : ∞ ∈ U
  · apply isClosed_compl_iff.mp
    rw [← preimage_compl,
      preimage_eq_image τ hτ.injective (show ∞ ∉ Uᶜ from not_not.mpr hinfty)]
    rw [preimage_compl]
    have hK : IsCompact ((((↑) : K → OnePoint K) ⁻¹' U)ᶜ) :=
      ((OnePoint.isOpen_iff_of_mem hinfty).mp hU).2
    exact ((isCompact_univ : IsCompact (univ : Set M)).prod hK).image
      hτ.continuous |>.isClosed
  · rw [preimage_eq_image τ hτ.injective hinfty]
    exact hτ.isOpenMap _ (isOpen_univ.prod ((OnePoint.isOpen_iff_of_notMem hinfty).mp hU))

theorem collapse_eq_coe_iff (hτ : Function.Injective τ) (y : Y) (k : K) :
    collapse τ y = (k : OnePoint K) ↔ ∃ m, τ (m, k) = y := by
  classical
  constructor
  · intro h
    by_cases hy : y ∈ range τ
    · have hs : (Classical.choose hy).2 = k := by
        apply OnePoint.coe_injective
        simpa only [collapse, dif_pos hy] using h
      refine ⟨(Classical.choose hy).1, ?_⟩
      rw [← hs]
      exact Classical.choose_spec hy
    · rw [collapse_of_not_mem τ hy] at h
      exact (OnePoint.infty_ne_coe k h).elim
  · rintro ⟨m, rfl⟩
    exact collapse_apply τ hτ (m, k)

noncomputable def collapseOnePoint (y : OnePoint Y) : OnePoint K :=
  collapse (fun p ↦ (τ p : OnePoint Y)) y

theorem continuous_collapseOnePoint [TopologicalSpace M] [TopologicalSpace K]
    [TopologicalSpace Y] [CompactSpace M] [T2Space Y] [LocallyCompactSpace Y]
    (hτ : IsOpenEmbedding τ) : Continuous (collapseOnePoint τ) :=
  continuous_collapse _ (OnePoint.isOpenEmbedding_coe.comp hτ)

theorem collapseOnePoint_infty : collapseOnePoint τ ∞ = ∞ := by
  apply collapse_of_not_mem
  rintro ⟨p, hp⟩
  exact OnePoint.coe_ne_infty (τ p) hp

theorem collapseOnePoint_eq_coe_iff (hτ : Function.Injective τ)
    (y : OnePoint Y) (k : K) :
    collapseOnePoint τ y = (k : OnePoint K) ↔ ∃ m, (τ (m, k) : OnePoint Y) = y :=
  collapse_eq_coe_iff _ (OnePoint.coe_injective.comp hτ) y k

end NoExoticSixSphere.OpenFiberCollapse
