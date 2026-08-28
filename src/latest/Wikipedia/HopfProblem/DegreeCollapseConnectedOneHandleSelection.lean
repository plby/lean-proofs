import Wikipedia.HopfProblem.DegreeCollapseOrderedMinimumCount

/-!
# Connectedness selects an actual one-handle joining old components

If there is more than one minimum, some actual index-one attaching sphere
has two points whose images are not joined in its original lower sublevel.
This selects a genuine component-merging handle. It does not yet put that
handle next to a selected minimum or assert a unique connecting orbit.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
  {f : M → ℝ} (S : SurgeryWindows E f)

theorem exists_native_one_handle_joining_components
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmin : nativeMorseCount E f 0 ≠ 1) :
    ∃ p : criticalPoints E f, nativeMorseIndex E f p = 1 ∧
      ∃ u v, ¬Joined ((S.data p).coreBoundaryMap u) ((S.data p).coreBoundaryMap v) := by
  classical
  by_contra h
  apply hmin
  apply native_minimum_count_one_of_one_handle_components S hf
  intro p hp
  have hindex : 0 < Module.finrank ℝ (S.data p).chart.NegativeCoordinates := by
    rw [← nativeMorseIndex_eq_chart (S.data p).chart, hp]
    exact zero_lt_one
  apply native_attaching_component_of_pairwise_joined (S.data p) hindex
  intro u v
  by_contra huv
  exact h ⟨p, hp, u, v, huv⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
