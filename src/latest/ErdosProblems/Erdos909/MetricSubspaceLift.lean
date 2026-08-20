/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set Topology TopologicalSpace

namespace Erdos909.MetricSubspaceLift

theorem exists_isOpen_subtype_lift_closure_preimage_eq
    {Z : Type*} [PseudoMetricSpace Z] (s : Set Z) {B : Set s}
    (hB : IsOpen B) (hBn : B.Nonempty) (hBc : Bᶜ.Nonempty) :
    ∃ V : Set Z, IsOpen V ∧
      Subtype.val ⁻¹' V = B ∧
      Subtype.val ⁻¹' closure V = closure B := by
  let A : Set Z := Subtype.val '' B
  let C : Set Z := Subtype.val '' Bᶜ
  let V : Set Z := {x | Metric.infDist x A < Metric.infDist x C}
  have hAn : A.Nonempty := hBn.image Subtype.val
  have hCn : C.Nonempty := hBc.image Subtype.val
  have hVo : IsOpen V :=
    isOpen_lt (Metric.continuous_infDist_pt A) (Metric.continuous_infDist_pt C)
  have htrace : Subtype.val ⁻¹' V = B := by
    ext y
    constructor
    · intro hyV
      by_contra hyB
      have hyC : (y : Z) ∈ C := ⟨y, hyB, rfl⟩
      have hzero : Metric.infDist (y : Z) C = 0 := Metric.infDist_zero_of_mem hyC
      exact (not_lt_of_ge Metric.infDist_nonneg) (by simpa [V, hzero] using hyV)
    · intro hyB
      have hyA : (y : Z) ∈ A := ⟨y, hyB, rfl⟩
      have hzero : Metric.infDist (y : Z) A = 0 := Metric.infDist_zero_of_mem hyA
      have hy_not : (y : Z) ∉ closure C := by
        have hy_not' : y ∉ closure (Bᶜ : Set s) := by
          rw [hB.isClosed_compl.closure_eq]
          simpa only [mem_compl_iff, not_not] using hyB
        simpa [C, IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] using hy_not'
      have hpos : 0 < Metric.infDist (y : Z) C :=
        (Metric.infDist_pos_iff_notMem_closure hCn).1 hy_not
      simpa [V, hzero] using hpos
  refine ⟨V, hVo, htrace, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hycl
    have hy_notA : (y : Z) ∉ closure A := by
      have hy_notA' : y ∉ closure B := hycl
      simpa [A, IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] using hy_notA'
    have hposA : 0 < Metric.infDist (y : Z) A :=
      (Metric.infDist_pos_iff_notMem_closure hAn).1 hy_notA
    have hyBc : y ∈ Bᶜ := by
      simpa using fun hyB : y ∈ B ↦ hycl (subset_closure hyB)
    have hyC : (y : Z) ∈ C := ⟨y, hyBc, rfl⟩
    have hzeroC : Metric.infDist (y : Z) C = 0 := Metric.infDist_zero_of_mem hyC
    let W : Set Z := {x | Metric.infDist x C < Metric.infDist x A}
    have hWo : IsOpen W :=
      isOpen_lt (Metric.continuous_infDist_pt C) (Metric.continuous_infDist_pt A)
    have hyW : (y : Z) ∈ W := by simpa [W, hzeroC] using hposA
    have hWV : W ⊆ Vᶜ := by
      intro x hx
      simp only [mem_compl_iff, mem_ofPred_eq, V, W] at hx ⊢
      exact fun h ↦ lt_asymm hx h
    have hyint : (y : Z) ∈ interior Vᶜ :=
      mem_interior_iff_mem_nhds.2
        (Filter.mem_of_superset (hWo.mem_nhds hyW) hWV)
    have : (y : Z) ∉ closure V := by
      simpa only [interior_compl, mem_compl_iff] using hyint
    exact this hy
  · intro y hy
    have hyA : (y : Z) ∈ closure A := by
      simpa [A, IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] using hy
    apply closure_mono _ hyA
    intro x hxA
    rcases hxA with ⟨y, hyB, rfl⟩
    change y ∈ Subtype.val ⁻¹' V
    rw [htrace]
    exact hyB

end Erdos909.MetricSubspaceLift
