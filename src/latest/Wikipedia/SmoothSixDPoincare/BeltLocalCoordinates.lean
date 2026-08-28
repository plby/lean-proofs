import Wikipedia.SmoothSixDPoincare.BeltSurgeryNeighborhood
import Wikipedia.SmoothSixDPoincare.OpenDiffeomorphPartial
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphProduct

/-!
# Full vector coordinates in the original belt neighborhood

A native chart on the belt sphere gives normal-times-transverse coordinates
in the actual upper level. The first coordinate is exactly the original
normalized Morse normal projection, and every value is retained from the
original belt-surgery diffeomorphism.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
def beltLocalCoordinates (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (χ : PartialDiffeomorph 𝓘(ℝ, F) (𝓡 n) F
      (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) ∞) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    PartialDiffeomorph 𝓘(ℝ, d.chart.NegativeCoordinates × F)
      𝓘(ℝ, RegularLevel.Model E) (d.chart.NegativeCoordinates × F) d.UpperLevel ∞ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let c := OpenDiffeomorph.partialDiffeomorph (d.beltSurgeryDiffeomorph hf n)
    ⟨(χ 0, 0), d.belt_zero_mem_surgerySource (χ 0)⟩
  let A := (Diffeomorph.prodComm 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, F)
    d.chart.NegativeCoordinates F ∞).toPartialDiffeomorph.trans
      ((PartialChart.prod χ (Diffeomorph.refl 𝓘(ℝ, d.chart.NegativeCoordinates)
        d.chart.NegativeCoordinates ∞).toPartialDiffeomorph).trans c)
  exact (PartialChart.vectorProduct d.chart.NegativeCoordinates F).toPartialDiffeomorph.trans A

open Classical in
theorem beltLocalCoordinates_source (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (χ : PartialDiffeomorph 𝓘(ℝ, F) (𝓡 n) F
      (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) ∞)
    (z : d.chart.NegativeCoordinates × F) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    z ∈ (d.beltLocalCoordinates hf n χ).source ↔
      z.2 ∈ χ.source ∧ (χ z.2, z.1) ∈ d.beltSurgerySource := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  change (z ∈ (univ : Set (d.chart.NegativeCoordinates × F)) ∧
    (z ∈ (univ : Set (d.chart.NegativeCoordinates × F)) ∧
    ((z.2 ∈ χ.source ∧ z.1 ∈ (univ : Set d.chart.NegativeCoordinates)) ∧
      (χ z.2, z.1) ∈ d.beltSurgerySource))) ↔ _
  simp only [mem_univ, true_and, and_true]

open Classical in
theorem beltLocalCoordinates_apply (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (χ : PartialDiffeomorph 𝓘(ℝ, F) (𝓡 n) F
      (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) ∞)
    (z : d.chart.NegativeCoordinates × F)
    (hz : (χ z.2, z.1) ∈ d.beltSurgerySource) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    d.beltLocalCoordinates hf n χ z = (d.beltSurgeryHomeomorph ⟨(χ z.2, z.1), hz⟩).val := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact OpenDiffeomorph.partialDiffeomorph_apply (d.beltSurgeryDiffeomorph hf n)
    ⟨(χ 0, 0), d.belt_zero_mem_surgerySource (χ 0)⟩ ⟨(χ z.2, z.1), hz⟩

open Classical in
theorem beltLocalCoordinates_zero (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (χ : PartialDiffeomorph 𝓘(ℝ, F) (𝓡 n) F
      (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) ∞) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    d.beltLocalCoordinates hf n χ (0 : d.chart.NegativeCoordinates × F) =
      d.surgery.beltSphere (χ 0) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  rw [d.beltLocalCoordinates_apply hf n χ 0 (d.belt_zero_mem_surgerySource (χ 0))]
  exact d.beltSurgeryHomeomorph_zero (χ 0)

open Classical in
theorem beltLocalCoordinates_normal (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (χ : PartialDiffeomorph 𝓘(ℝ, F) (𝓡 n) F
      (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) ∞) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ z ∈ (d.beltLocalCoordinates hf n χ).source,
      d.beltNormal (d.beltLocalCoordinates hf n χ z) = d.radius • z.1 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro z hz
  have hzs := ((d.beltLocalCoordinates_source hf n χ z).mp hz).2
  rw [d.beltLocalCoordinates_apply hf n χ z hzs]
  exact d.beltNormal_beltSurgeryHomeomorph ⟨(χ z.2, z.1), hzs⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
