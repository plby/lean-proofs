import Wikipedia.SmoothSixDPoincare.AnnularPatchInclusion
import Wikipedia.SmoothSixDPoincare.SmoothBeltNeighborhood

/-!
# The upper annular coordinates form a full native partial diffeomorphism

The exact smooth annular exchange and the original belt-neighborhood
diffeomorphism compose with their actual open inclusions. Their point map
is the upper annular map appearing in the corrected realization formula.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open PuncturedHandle FramedSurgery MorseHandle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (m n : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]

open Classical in
def annularBeltRawPartial :
    PartialDiffeomorph ((𝓡 m).prod 𝓘(ℝ, d.chart.PositiveCoordinates))
      ((𝓡 n).prod 𝓘(ℝ, d.chart.NegativeCoordinates))
      (AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates)
      (UnitSphere d.chart.PositiveCoordinates × d.chart.NegativeCoordinates) ∞ :=
  (annularExchange m n).toPartialDiffeomorph.trans (annularInclusionPartial n m)

open Classical in
theorem annularBeltRawPartial_source : (d.annularBeltRawPartial m n).source = univ := by
  apply eq_univ_of_forall
  intro z
  refine ⟨mem_univ _, ?_⟩
  change annularExchange m n z ∈ (annularInclusionPartial n m).source
  rw [annularInclusionPartial_source]
  trivial

open Classical in
theorem annularBeltRawPartial_point
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    d.annularBeltRawPartial m n z = annularBeltCoordinates z :=
  annularExchange_coordinates m n z

open Classical in
theorem annularBeltRawPartial_mem
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    d.annularBeltRawPartial m n z ∈ d.chart.beltSource d.radius d.radius_pos :=
  d.annularBeltCoordinates_mem z

open Classical in
def annularBeltSourcePartial :
    PartialDiffeomorph ((𝓡 m).prod 𝓘(ℝ, d.chart.PositiveCoordinates))
      ((𝓡 n).prod 𝓘(ℝ, d.chart.NegativeCoordinates))
      (AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates)
      (d.chart.beltSource d.radius d.radius_pos) ∞ := by
  let _ := nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n
  exact PartialChart.intoOpen (d.annularBeltRawPartial m n)
    (d.chart.beltSource d.radius d.radius_pos) (d.annularBeltRawPartial_mem m n)

open Classical in
theorem annularBeltSourcePartial_source : (d.annularBeltSourcePartial m n).source = univ := by
  let _ := nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n
  exact PartialChart.intoOpen_source (d.annularBeltRawPartial m n)
    (d.chart.beltSource d.radius d.radius_pos) (d.annularBeltRawPartial_mem m n)
      (d.annularBeltRawPartial_source m n)

open Classical in
theorem annularBeltSourcePartial_point
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    d.annularBeltSourcePartial m n z = d.annularBeltPoint z := by
  let _ := nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n
  apply Subtype.ext
  exact (PartialChart.intoOpen_apply (d.annularBeltRawPartial m n)
    (d.chart.beltSource d.radius d.radius_pos) (d.annularBeltRawPartial_mem m n) z).trans
      (d.annularBeltRawPartial_point m n z)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
def annularUpperPartial :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    PartialDiffeomorph ((𝓡 m).prod 𝓘(ℝ, d.chart.PositiveCoordinates))
      𝓘(ℝ, RegularLevel.Model E)
      (AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates)
      d.UpperLevel ∞ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let z₀ := Classical.choice (nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n)
  let _ : Nonempty (d.chart.beltTarget d.radius) :=
    ⟨d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (d.annularBeltPoint z₀)⟩
  exact ((d.annularBeltSourcePartial m n).trans
    (d.chart.beltNeighborhoodDiffeomorph hf n d.radius d.radius_pos
      d.upper_regular).toPartialDiffeomorph).trans
    (PartialChart.openInclusion (d.chart.beltTarget d.radius))

open Classical in
theorem annularUpperPartial_source :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (d.annularUpperPartial m n hf).source = univ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  apply eq_univ_of_forall
  intro z
  refine ⟨⟨?_, mem_univ _⟩, mem_univ _⟩
  change z ∈ (d.annularBeltSourcePartial m n).source
  rw [d.annularBeltSourcePartial_source]
  trivial

open Classical in
theorem annularUpperPartial_point
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    d.annularUpperPartial m n hf z = d.annularUpperPoint z := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact congrArg (fun w : d.chart.beltSource d.radius d.radius_pos =>
    (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos w).val)
      (d.annularBeltSourcePartial_point m n z)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
