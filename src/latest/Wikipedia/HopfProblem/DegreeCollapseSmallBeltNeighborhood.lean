import Wikipedia.HopfProblem.DegreeCollapseNormalBoundaryMeridian

/-!
# Choose the actual small belt neighborhood inside any parameter neighborhood

Continuity at the crossing forces both membership in the original Morse
chart and a normal coordinate smaller than the fixed tube radius. No
local meridian comparison or geometric neighborhood is assumed as data.
-/

noncomputable section

open Set Function Metric Filter ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem exists_small_native_belt_neighborhood (d : MorseSurgeryData E f p)
    (G : A → d.UpperLevel) (v : sphere (0 : d.chart.PositiveCoordinates) 1)
    {t : Set A} (ht : t ∈ 𝓝 (0 : A)) (hc : ContinuousOn G t)
    (hcenter : G 0 = d.surgery.beltSphere v) :
    ∃ s : Set A, s ∈ 𝓝 (0 : A) ∧ s ⊆ t ∧ ContinuousOn G s ∧
      (∀ z ∈ s, G z ∈ d.beltNormalDomain) ∧
      (∀ z ∈ s, ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1) := by
  have hG : ContinuousAt G 0 := hc.continuousAt ht
  have hdomain : G 0 ∈ d.beltNormalDomain := hcenter ▸ d.belt_mem_normalDomain v
  have hsplit : ContinuousAt d.chart.splitChart (G 0).val :=
    d.chart.splitChart.contMDiffOn_toFun.continuousOn.continuousAt
      (d.chart.splitChart.open_source.mem_nhds hdomain)
  have hGM : ContinuousAt (fun z : A => (G z).val) 0 :=
    (continuous_subtype_val : Continuous (Subtype.val : d.UpperLevel → M)).continuousAt.comp hG
  have hsplitG : ContinuousAt (fun z : A => d.chart.splitChart (G z).val) 0 :=
    ContinuousAt.comp (f := fun z : A => (G z).val) hsplit hGM
  have hnormal : ContinuousAt (fun z => d.beltNormal (G z)) 0 := by
    change ContinuousAt (fun z : A => (d.chart.splitChart (G z).val).1) 0
    exact hsplitG.fst
  have hsize : ContinuousAt (fun z => ‖d.radius⁻¹ • d.beltNormal (G z)‖) 0 :=
    (hnormal.const_smul d.radius⁻¹).norm
  have hzero : ‖d.radius⁻¹ • d.beltNormal (G 0)‖ < 1 := by
    rw [hcenter, d.beltNormal_belt, smul_zero, norm_zero]
    norm_num
  have h₀ : G ⁻¹' d.beltNormalDomain ∈ 𝓝 (0 : A) :=
    hG.preimage_mem_nhds (d.isOpen_beltNormalDomain.mem_nhds hdomain)
  have h₁ : {z : A | ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1} ∈ 𝓝 (0 : A) :=
    hsize.preimage_mem_nhds (Iio_mem_nhds hzero)
  let s := t ∩ (G ⁻¹' d.beltNormalDomain ∩ {z : A | ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1})
  refine ⟨s, inter_mem ht (inter_mem h₀ h₁), inter_subset_left,
    hc.mono inter_subset_left, ?_, ?_⟩
  · intro z hz
    exact hz.2.1
  · intro z hz
    exact hz.2.2

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
