import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith

/-!
# A uniform closed normal disk over a compact base

An open neighborhood of the zero section in a product contains a product
with one fixed positive-radius closed ball. The tube lemma gives uniformity.
-/

open Set

namespace NoExoticSixSphere

theorem exists_uniform_closedProductTube {X F : Type*}
    [TopologicalSpace X] [CompactSpace X] [NormedAddCommGroup F]
    {U : Set (X × F)} (hU : IsOpen U) (hzero : ∀ x, (x, (0 : F)) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ x v, ‖v‖ ≤ r → (x, v) ∈ U := by
  have hp : (univ : Set X) ×ˢ ({0} : Set F) ⊆ U := by
    rintro ⟨x, v⟩ ⟨_, hv⟩
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact hzero x
  obtain ⟨V, W, _, hW, hV, hz, hVW⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hU hp
  have h0 : (0 : F) ∈ W := hz (mem_singleton 0)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0)
  refine ⟨δ / 2, by linarith, fun x v hv ↦ ?_⟩
  apply hVW
  refine ⟨hV (mem_univ x), hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  linarith

end NoExoticSixSphere
