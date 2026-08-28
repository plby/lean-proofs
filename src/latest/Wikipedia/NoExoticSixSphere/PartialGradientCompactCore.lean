import Wikipedia.NoExoticSixSphere.PartialGradientFiberCore
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact fiber cores in an arbitrarily prescribed neighborhood

The sum of the center and displacement bounds controls the ambient norm.
Thus fiber cores have compact closure in a proper ambient space, and their
closures can be chosen inside any open neighborhood of zero. This applies
to the finite-dimensional polygon chart models.
-/

open Set
open scoped Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

theorem closure_fiberCore_subset_closedBall (a b : ℝ) :
    closure (C.fiberCore a b) ⊆ Metric.closedBall 0 (a + b) :=
  closure_minimal ((C.fiberCore_subset_ball a b).trans Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall

variable [ProperSpace E]

theorem isCompact_closure_fiberCore (a b : ℝ) : IsCompact (closure (C.fiberCore a b)) :=
  (isCompact_closedBall (0 : E) (a + b)).of_isClosed_subset isClosed_closure
    (C.closure_fiberCore_subset_closedBall a b)

theorem exists_compact_fiberCore_in (N : Set E) (hN : IsOpen N) (hzero : (0 : E) ∈ N) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ IsCompact (closure (C.fiberCore a b)) ∧
      closure (C.fiberCore a b) ⊆ N := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hN.mem_nhds hzero)
  refine ⟨r / 4, r / 4, by positivity, by positivity,
    C.isCompact_closure_fiberCore _ _, ?_⟩
  exact (C.closure_fiberCore_subset_closedBall _ _).trans
    ((Metric.closedBall_subset_ball (by linarith : r / 4 + r / 4 < r)).trans hball)

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
