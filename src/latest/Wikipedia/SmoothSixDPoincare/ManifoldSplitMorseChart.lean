import Wikipedia.SmoothSixDPoincare.ManifoldMorseNormalForm
import Wikipedia.SmoothSixDPoincare.SignedSplitCoordinates

/-!
# Product Euclidean Morse coordinates on the original manifold

The negative and positive coordinate blocks are composed with the actual
smooth Morse chart. A genuine product of small closed Euclidean balls fits
inside its target, ready for the local handle construction.
-/

noncomputable section

open Set Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} (c : SignedMorseChart (E := E) f x)

abbrev NegativeCoordinates := MorseHandle.NegativeSpace c.weights
abbrev PositiveCoordinates := MorseHandle.PositiveSpace c.weights

open Classical in
theorem finrank_negative_add_positive :
    Module.finrank ℝ c.NegativeCoordinates + Module.finrank ℝ c.PositiveCoordinates =
      Module.finrank ℝ E := by
  have h := (MorseHandle.splitLinearEquiv c.weights).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using h.symm

open Classical in
/-- The original Morse chart with its negative and positive Euclidean coordinates separated. -/
def splitChart : PartialDiffeomorph 𝓘(ℝ, E)
    𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates)
    M (c.NegativeCoordinates × c.PositiveCoordinates) ∞ :=
  c.chart.trans (MorseHandle.splitCoordinates c.weights).toDiffeomorph.toPartialDiffeomorph

open Classical in
theorem splitChart_mem_source : x ∈ c.splitChart.source := ⟨c.mem_source, mem_univ _⟩

open Classical in
@[simp] theorem splitChart_center : c.splitChart x = 0 := by
  change MorseHandle.splitCoordinates c.weights (c.chart x) = 0
  rw [c.center, map_zero]

open Classical in
/-- The function has its genuine difference-of-norm-squares form in product coordinates. -/
theorem splitChart_equation {y : M} (hy : y ∈ c.splitChart.source) :
    f y = f x - ‖(c.splitChart y).1‖ ^ 2 + ‖(c.splitChart y).2‖ ^ 2 := by
  rw [c.equation y hy.1, MorseHandle.signedSum_eq_norms c.weights c.signs]
  change f x + (-‖(c.splitChart y).1‖ ^ 2 + ‖(c.splitChart y).2‖ ^ 2) = _
  ring

open Classical in
/-- The inverse chart also satisfies the exact function identity. -/
theorem splitChart_inverse_equation {y : c.NegativeCoordinates × c.PositiveCoordinates}
    (hy : y ∈ c.splitChart.target) :
    f (c.splitChart.symm y) = f x - ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
  change f (c.chart.symm ((MorseHandle.splitCoordinates c.weights).symm y)) = _
  rw [c.inverse_equation ((MorseHandle.splitCoordinates c.weights).symm y) hy.2,
    MorseHandle.signedSum_symm_eq_norms c.weights c.signs]
  ring

open Classical in
/-- A closed product block of positive radius lies inside the actual Morse chart. -/
theorem exists_closed_productBlock :
    ∃ r > (0 : ℝ),
      closedBall (0 : c.NegativeCoordinates) r ×ˢ
        closedBall (0 : c.PositiveCoordinates) r ⊆ c.splitChart.target := by
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.toOpenPartialHomeomorph.map_source c.splitChart_mem_source
  obtain ⟨r, hr, hsub⟩ := nhds_basis_closedBall.mem_iff.mp
    (c.splitChart.open_target.mem_nhds hzero)
  refine ⟨r, hr, ?_⟩
  rw [closedBall_prod_same]
  exact hsub

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
