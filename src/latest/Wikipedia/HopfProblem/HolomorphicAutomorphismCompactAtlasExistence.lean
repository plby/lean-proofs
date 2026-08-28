import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith

/-!
# Finite nested neighborhoods in the original atlas

Each preferred chart contains a closed coordinate ball of three times
some positive radius. The corresponding open balls of the smaller radius
cover the compact charted space, so finitely many actual chart centers
suffice. No finite-dimensionality or properness assumption is needed.
-/

open Set

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism

/-- Choose positive radii in the unchanged native charts, with room for
threefold enlargement, and finitely many centers whose inner balls cover. -/
theorem exists_native_chart_radii_finite_cover (E M : Type*)
    [NormedAddCommGroup E] [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] :
    ∃ r : M → ℝ,
      (∀ x, 0 < r x ∧
        Metric.closedBall (chartAt E x x) (3 * r x) ⊆ (chartAt E x).target) ∧
      ∃ s : Finset M, ∀ y : M, ∃ x ∈ s,
        y ∈ (chartAt E x).source ∧
        chartAt E x y ∈ Metric.ball (chartAt E x x) (r x) := by
  classical
  have hradii : ∀ x : M, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (chartAt E x x) (3 * r) ⊆ (chartAt E x).target := by
    intro x
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (chartAt E x).open_target
      (chartAt E x x) ((chartAt E x).map_source (mem_chart_source E x))
    refine ⟨ε / 4, by linarith, ?_⟩
    exact (Metric.closedBall_subset_ball (show 3 * (ε / 4) < ε by linarith)).trans hball
  choose r hr using hradii
  let U : M → Set M := fun x =>
    (chartAt E x).source ∩ (chartAt E x) ⁻¹' Metric.ball (chartAt E x x) (r x)
  have hU : ∀ x, IsOpen (U x) := fun x =>
    (chartAt E x).isOpen_inter_preimage Metric.isOpen_ball
  have hcover : (univ : Set M) ⊆ ⋃ x : M, U x := by
    intro y _
    exact mem_iUnion.mpr ⟨y, mem_chart_source E y, Metric.mem_ball_self (hr y).1⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨r, hr, s, ?_⟩
  intro y
  obtain ⟨x, hxs, hy⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  exact ⟨x, hxs, hy.1, hy.2⟩

end Wikipedia.HopfProblem.HolomorphicAutomorphism
