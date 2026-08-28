import Wikipedia.SmoothSixDPoincare.PartialChartVectorField
import Wikipedia.SmoothSixDPoincare.MorseDescentModel
import Wikipedia.SmoothSixDPoincare.ManifoldSplitMorseChart

/-!
# A native descending vector field in each genuine Morse chart

The pulled-back linear field is smooth on the chart source, vanishes at
the critical center, and strictly decreases the original manifold function
at every other point of the chart.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
def descentField : (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  FlowConstruction.partialChartField c.splitChart MorseHandle.descent

open Classical in
theorem contMDiffOn_descentField [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M] :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, c.descentField x⟩ : TangentBundle 𝓘(ℝ, E) M)) c.splitChart.source :=
  FlowConstruction.contMDiffOn_partialChartField c.splitChart MorseHandle.contDiff_descent

open Classical in
@[simp] theorem descentField_center : c.descentField p = 0 := by
  have hzero : MorseHandle.descent (c.splitChart p) = 0 := by
    rw [c.splitChart_center]
    simp [MorseHandle.descent]
  unfold descentField FlowConstruction.partialChartField
  rw [VectorField.mpullback_apply, hzero, map_zero, map_zero]

open Classical in
/-- The derivative is a negative multiple of the sum of the squared coordinate norms. -/
theorem mvfderiv_descentField
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : x ∈ c.splitChart.source) :
    mvfderiv 𝓘(ℝ, E) f x (c.descentField x) =
      -2 * (‖(c.splitChart x).1‖ ^ 2 + ‖(c.splitChart x).2‖ ^ 2) := by
  rw [descentField, FlowConstruction.mvfderiv_partialChartField hf c.splitChart _ hx]
  have hcoord : (f ∘ c.splitChart.symm) =ᶠ[𝓝 (c.splitChart x)]
      (fun z => f p + MorseHandle.quadratic z) := by
    filter_upwards [c.splitChart.open_target.mem_nhds
      (c.splitChart.toOpenPartialHomeomorph.map_source hx)] with z hz
    change f (c.splitChart.symm z) = f p + (-‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
    rw [c.splitChart_inverse_equation hz]
    ring
  rw [hcoord.fderiv_eq, fderiv_const_add]
  exact MorseHandle.fderiv_quadratic_descent _

open Classical in
theorem mvfderiv_descentField_nonpos
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : x ∈ c.splitChart.source) :
    mvfderiv 𝓘(ℝ, E) f x (c.descentField x) ≤ 0 := by
  rw [c.mvfderiv_descentField hf hx]
  nlinarith [sq_nonneg ‖(c.splitChart x).1‖, sq_nonneg ‖(c.splitChart x).2‖]

open Classical in
/-- Except at the chart's center, this field strictly decreases the original function. -/
theorem mvfderiv_descentField_neg
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : x ∈ c.splitChart.source)
    (hxp : x ≠ p) : mvfderiv 𝓘(ℝ, E) f x (c.descentField x) < 0 := by
  have hcoord : c.splitChart x ≠ 0 := by
    intro h
    apply hxp
    exact c.splitChart.toOpenPartialHomeomorph.injOn hx c.splitChart_mem_source
      (h.trans c.splitChart_center.symm)
  rw [c.mvfderiv_descentField hf hx]
  simpa only [MorseHandle.fderiv_quadratic_descent] using
    MorseHandle.fderiv_quadratic_descent_neg hcoord

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
