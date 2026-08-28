import Wikipedia.SmoothSixDPoincare.NativeTopIndexSmoothBody
import Wikipedia.SmoothSixDPoincare.RegularLevelTangent

/-!
# The actual sphere component filled by a native Morse cap

The capped component has standard smooth sphere coordinates in the original
lower-level atlas. Their inverse is the negative Morse coordinate divided
by the original radius. This retains smooth data that a topological cap
parametrization alone would not supply.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem attaching_model_mem_target (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    (d.radius • (u : d.chart.NegativeCoordinates), 0) ∈ d.chart.splitChart.target := by
  apply d.block
  constructor
  · have hu : ‖(u : d.chart.NegativeCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos d.radius_pos, hu, mul_one]
    linarith [d.radius_pos]
  · simpa only [mem_closedBall, dist_self] using
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) d.radius_pos.le)

open Classical in
theorem attaching_mem_splitChart (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    (d.surgery.attachingSphere u : M) ∈ d.chart.splitChart.source := by
  rw [d.attaching_eq, d.chart.attachingCoreMap_coe]
  exact d.chart.splitChart.map_target' (d.attaching_model_mem_target u)

open Classical in
theorem attaching_split_coordinates (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    d.chart.splitChart (d.surgery.attachingSphere u : M) =
      (d.radius • (u : d.chart.NegativeCoordinates), 0) := by
  rw [d.attaching_eq, d.chart.attachingCoreMap_coe]
  exact d.chart.splitChart.right_inv' (d.attaching_model_mem_target u)

variable (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E)

open Classical in
def topIndexCapOpen : TopologicalSpace.Opens d.LowerLevel := by
  let _ := d.subsingleton_positive_of_top_index hindex
  exact d.surgery.reverse.bornOpen

open Classical in
def topIndexCapCoordinates :
    PuncturedHandle.UnitSphere d.chart.NegativeCoordinates ≃ₜ d.topIndexCapOpen hindex := by
  let _ := d.subsingleton_positive_of_top_index hindex
  exact d.surgery.reverse.bornCoordinates

open Classical in
theorem topIndexCapCoordinates_coe (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    (d.topIndexCapCoordinates hindex u).val = d.surgery.attachingSphere u := rfl

open Classical in
theorem topIndexCapCoordinates_symm_vector (y : d.topIndexCapOpen hindex) :
    ((d.topIndexCapCoordinates hindex).symm y).val =
      d.radius⁻¹ • (d.chart.splitChart (y.val : M)).1 := by
  obtain ⟨u, rfl⟩ := (d.topIndexCapCoordinates hindex).surjective y
  rw [Homeomorph.symm_apply_apply]
  change (u : d.chart.NegativeCoordinates) =
    d.radius⁻¹ • (d.chart.splitChart (d.surgery.attachingSphere u : M)).1
  rw [d.attaching_split_coordinates]
  exact (inv_smul_smul₀ d.radius_pos.ne' (u : d.chart.NegativeCoordinates)).symm

open Classical in
theorem topIndexCap_mem_splitChart (y : d.topIndexCapOpen hindex) :
    (y.val : M) ∈ d.chart.splitChart.source := by
  obtain ⟨u, rfl⟩ := (d.topIndexCapCoordinates hindex).surjective y
  exact d.attaching_mem_splitChart u

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (n : ℕ) [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)]

open Classical in
theorem topIndexCapCoordinates_contMDiff :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ (d.topIndexCapCoordinates hindex) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  apply (ContMDiff.subtypeVal_comp_iff (d.topIndexCapOpen hindex) _).mp
  change ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.surgery.attachingSphere
  exact d.attaching_smooth hf n

open Classical in
theorem topIndexCapCoordinates_symm_contMDiff :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ContMDiff 𝓘(ℝ, RegularLevel.Model E) (𝓡 n) ∞ (d.topIndexCapCoordinates hindex).symm := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.isManifold hf d.lower_regular
  have hi : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞
      (fun y : d.topIndexCapOpen hindex => (y.val : M)) :=
    (RegularLevel.contMDiff_inclusion hf d.lower_regular).comp contMDiff_subtype_val
  have hc : ContMDiff 𝓘(ℝ, RegularLevel.Model E)
      𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
      (fun y : d.topIndexCapOpen hindex => d.chart.splitChart (y.val : M)) :=
    d.chart.splitChart.contMDiffOn_toFun.comp_contMDiff hi (d.topIndexCap_mem_splitChart hindex)
  have hv : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞
      (fun y : d.topIndexCapOpen hindex => ((d.topIndexCapCoordinates hindex).symm y).val) := by
    have hs : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, ℝ) ∞
        (fun _ : d.topIndexCapOpen hindex => d.radius⁻¹) := contMDiff_const
    have hp : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞
        (fun y : d.topIndexCapOpen hindex => (d.chart.splitChart (y.val : M)).1) :=
      contDiff_fst.contMDiff.comp hc
    exact (hs.smul hp).congr
      (fun y => d.topIndexCapCoordinates_symm_vector hindex y)
  exact hv.codRestrict_sphere (fun y => ((d.topIndexCapCoordinates hindex).symm y).property)

open Classical in
def topIndexCapDiffeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    Diffeomorph (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
      (PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) (d.topIndexCapOpen hindex) ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  exact {
    toEquiv := (d.topIndexCapCoordinates hindex).toEquiv
    contMDiff_toFun := d.topIndexCapCoordinates_contMDiff hindex hf n
    contMDiff_invFun := d.topIndexCapCoordinates_symm_contMDiff hindex hf n }

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
