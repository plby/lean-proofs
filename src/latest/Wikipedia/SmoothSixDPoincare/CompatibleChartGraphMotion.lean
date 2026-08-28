import Wikipedia.SmoothSixDPoincare.CompatibleWhitneyChart
import Wikipedia.SmoothSixDPoincare.GraphMotionCutoff
import Wikipedia.SmoothSixDPoincare.UniformSupportedBumpIsotopy

/-!
# Actual graph-motion data inside the constructed compatible chart

The compact graph trace and its jointly smooth cutoff are constructed inside
the actual native chart source, without a fixed-cutoff containment assumption
or an extra smallness condition on the original bigon height. Uniform small
native motions are available for all slices of this cutoff family. Their
finite composition and the final cancellation are the next obligations.
-/

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon.CompatibleChart

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  {tube : TubularBigon (E := E) S T a b k.map l.map h}

theorem nonempty_graphMotionData (c : CompatibleChart tube) :
    Nonempty (GraphMotionData h c.chart.source) :=
  WhitneyPairModel.nonempty_graphMotionData tube.height_pos c.chart.open_source
    (fun _ hp => c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩)

end Wikipedia.SmoothSixDPoincare.TubularBigon.CompatibleChart
