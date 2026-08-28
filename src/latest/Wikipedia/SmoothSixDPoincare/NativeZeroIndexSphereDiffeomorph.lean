import Wikipedia.SmoothSixDPoincare.NativeZeroIndexSmoothBody
import Wikipedia.SmoothSixDPoincare.MorseBeltNormalCoordinates

/-!
# The actual boundary of a native disk birth is smoothly a standard sphere

The original born-sphere homeomorphism and its inverse are smooth in the
native upper-level atlas. The inverse is the positive Morse coordinate
scaled by the original radius. No smoothness is inferred from a merely
topological disk identification.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)

open Classical in
theorem zeroIndexBornCoordinates_symm_vector (y : d.zeroIndexBornOpen hindex) :
    ((d.zeroIndexBornCoordinates hindex).symm y).val =
      d.radius⁻¹ • (d.chart.splitChart (y.val : M)).2 := by
  obtain ⟨v, rfl⟩ := (d.zeroIndexBornCoordinates hindex).surjective y
  rw [Homeomorph.symm_apply_apply]
  change (v : d.chart.PositiveCoordinates) =
    d.radius⁻¹ • (d.chart.splitChart (d.surgery.beltSphere v : M)).2
  rw [d.belt_split_coordinates]
  exact (inv_smul_smul₀ d.radius_pos.ne' (v : d.chart.PositiveCoordinates)).symm

open Classical in
theorem zeroIndexBorn_mem_splitChart (y : d.zeroIndexBornOpen hindex) :
    (y.val : M) ∈ d.chart.splitChart.source := by
  obtain ⟨v, rfl⟩ := (d.zeroIndexBornCoordinates hindex).surjective y
  exact d.belt_mem_normalDomain v

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]

omit [T2Space M] [CompactSpace M] in
open Classical in
theorem zeroIndexBornCoordinates_contMDiff :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ (d.zeroIndexBornCoordinates hindex) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  apply (ContMDiff.subtypeVal_comp_iff (d.zeroIndexBornOpen hindex) _).mp
  change ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.surgery.beltSphere
  rw [d.belt_eq]
  exact d.chart.contMDiff_beltCoreMap n hf d.radius d.radius_pos d.block d.upper_regular

omit [T2Space M] [CompactSpace M] in
open Classical in
theorem zeroIndexBornCoordinates_symm_contMDiff :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff 𝓘(ℝ, RegularLevel.Model E) (𝓡 n) ∞ (d.zeroIndexBornCoordinates hindex).symm := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  have hi : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞
      (fun y : d.zeroIndexBornOpen hindex => (y.val : M)) :=
    (RegularLevel.contMDiff_inclusion hf d.upper_regular).comp contMDiff_subtype_val
  have hc : ContMDiff 𝓘(ℝ, RegularLevel.Model E)
      𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
      (fun y : d.zeroIndexBornOpen hindex => d.chart.splitChart (y.val : M)) :=
    d.chart.splitChart.contMDiffOn_toFun.comp_contMDiff hi (d.zeroIndexBorn_mem_splitChart hindex)
  have hv : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.PositiveCoordinates) ∞
      (fun y : d.zeroIndexBornOpen hindex => ((d.zeroIndexBornCoordinates hindex).symm y).val) := by
    have hs : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, ℝ) ∞
        (fun _ : d.zeroIndexBornOpen hindex => d.radius⁻¹) := contMDiff_const
    have hp : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.PositiveCoordinates) ∞
        (fun y : d.zeroIndexBornOpen hindex => (d.chart.splitChart (y.val : M)).2) :=
      contDiff_snd.contMDiff.comp hc
    exact (hs.smul hp).congr
      (fun y => d.zeroIndexBornCoordinates_symm_vector hindex y)
  exact hv.codRestrict_sphere (fun y => ((d.zeroIndexBornCoordinates hindex).symm y).property)

open Classical in
def zeroIndexBornDiffeomorph :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Diffeomorph (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
      (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) (d.zeroIndexBornOpen hindex) ∞ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact {
    toEquiv := (d.zeroIndexBornCoordinates hindex).toEquiv
    contMDiff_toFun := d.zeroIndexBornCoordinates_contMDiff hindex hf n
    contMDiff_invFun := d.zeroIndexBornCoordinates_symm_contMDiff hindex hf n }

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
